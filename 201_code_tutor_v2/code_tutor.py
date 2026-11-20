#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Code Tutor v5 — 코드 학습용 정적 분석기 + 오프라인 인터랙티브 튜터 생성기
=====================================================================
설계 원칙: "구조·해설·추적은 코드(AST)가 100% 결정적으로 만들고, LLM은 함수 단위의
짧은 문장만 담당한다. LLM 출력은 전부 검증하고, 실패하면 정적 해설로 자동 대체한다."

- 외부 패키지 0개 (표준 라이브러리만 사용 · 폐쇄망 OK · 결과 HTML도 CDN 없이 오프라인 동작)
- LLM 은 선택 사항이며 특정 모델에 종속되지 않음 (OpenAI 호환 /v1/chat/completions)

사용법
  python code_tutor.py                      # GUI
  python code_tutor.py <프로젝트폴더>         # CLI (LLM 설정이 있으면 사용)
  python code_tutor.py <프로젝트폴더> --no-llm
  python code_tutor.py -h
"""
from __future__ import annotations

import argparse
import ast
import builtins
import hashlib
import io
import json
import keyword
import math
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import tokenize
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import zlib

if sys.stdout is None:
    sys.stdout = open(os.devnull, "w", encoding="utf-8")
if sys.stderr is None:
    sys.stderr = open(os.devnull, "w", encoding="utf-8")
from collections import Counter, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple

VERSION = "6.0"
PROMPT_VERSION = "p6.0"
IGNORE_DIRS = {
    ".git", ".hg", ".svn", "__pycache__", ".venv", "venv", "env", ".env", ".tox",
    ".mypy_cache", ".pytest_cache", ".ruff_cache", "build", "dist", "node_modules",
    "site-packages", ".idea", ".vscode", ".code_tutor_cache", "wheels", "workspaces",
}
MAX_FILE_BYTES = 1_500_000
BUILTINS = set(dir(builtins))
CONFIG_PATH = Path.home() / ".code_tutor_config.json"
WORKSPACES_ROOT = Path(__file__).resolve().parent / "workspaces"

_TS_LANGS: Dict[str, Any] = {}
try:
    import tree_sitter as _ts  # type: ignore
    for _k, _mod, _attr in [
        ("c", "tree_sitter_c", "language"),
        ("cpp", "tree_sitter_cpp", "language"),
        ("js", "tree_sitter_javascript", "language"),
        ("ts", "tree_sitter_typescript", "language_typescript"),
        ("tsx", "tree_sitter_typescript", "language_tsx"),
    ]:
        try:
            _m = __import__(_mod)
            _TS_LANGS[_k] = _ts.Language(getattr(_m, _attr)())
        except Exception:
            pass
except ImportError:
    _ts = None

LANG_EXTS = {
    ".py": "py",
    ".js": "js", ".jsx": "js", ".mjs": "js", ".cjs": "js",
    ".ts": "ts", ".tsx": "tsx",
    ".c": "c", ".h": "c",
    ".cpp": "cpp", ".cc": "cpp", ".cxx": "cpp", ".hpp": "cpp", ".hh": "cpp", ".hxx": "cpp",
    ".m": "matlab",
}
LANG_LABELS = {
    "py": "Python", "js": "JavaScript", "ts": "TypeScript", "tsx": "TypeScript (TSX)",
    "c": "C", "cpp": "C++", "matlab": "MATLAB",
}
LANG_KWS = {
    "js": {"async", "await", "break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete",
           "do", "else", "export", "extends", "finally", "for", "from", "function", "if", "import", "in", "instanceof",
           "let", "new", "of", "return", "static", "super", "switch", "throw", "try", "typeof", "var", "void", "while",
           "with", "yield", "true", "false", "null", "undefined"},
    "c": {"auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else", "enum", "extern",
          "float", "for", "goto", "if", "inline", "int", "long", "register", "restrict", "return", "short", "signed",
          "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned", "void", "volatile", "while", "NULL",
          "true", "false", "bool"},
    "cpp": {"alignas", "alignof", "auto", "bool", "break", "case", "catch", "char", "class", "const", "constexpr",
            "continue", "decltype", "default", "delete", "do", "double", "dynamic_cast", "else", "enum", "explicit",
            "export", "extern", "false", "final", "float", "for", "friend", "goto", "if", "inline", "int", "long",
            "mutable", "namespace", "new", "noexcept", "nullptr", "operator", "override", "private", "protected",
            "public", "register", "return", "short", "signed", "sizeof", "static", "static_cast", "struct", "switch",
            "template", "throw", "true", "try", "typedef", "typename", "union", "unsigned", "using", "virtual", "void",
            "volatile", "while", "std"},
    "matlab": {"break", "case", "catch", "classdef", "continue", "else", "elseif", "end", "for", "function", "global",
               "if", "otherwise", "parfor", "persistent", "return", "spmd", "switch", "try", "while", "methods",
               "properties", "events", "enumeration", "true", "false"},
}
LANG_KWS["ts"] = LANG_KWS["js"] | {"interface", "type", "enum", "implements", "private", "protected", "public",
                                    "readonly", "abstract", "as", "is", "keyof", "namespace", "declare", "any",
                                    "number", "string", "boolean", "unknown", "never"}
LANG_KWS["tsx"] = LANG_KWS["ts"]

KB_FOREIGN = {
    "console.log": "콘솔에 디버그 출력", "fetch": "HTTP 네트워크 요청 보내기", "JSON.parse": "JSON 문자열 → 객체 파싱",
    "JSON.stringify": "객체 → JSON 문자열 변환", "document.querySelector": "DOM 요소 1개 선택",
    "document.querySelectorAll": "일치하는 DOM 요소 모두 선택", "addEventListener": "이벤트 리스너(콜백) 등록",
    "setTimeout": "일정 시간 뒤 콜백 실행", "setInterval": "일정 간격으로 반복 실행",
    "Promise.all": "여러 비동기 작업 동시 대기", "Array.from": "반복 가능 객체를 배열로 변환",
    "Object.keys": "객체의 키 배열 반환", "Object.entries": "[키, 값] 쌍 배열 반환",
    "map": "배열 각 원소 변환", "filter": "조건에 맞는 원소만 추출", "forEach": "배열 순회", "reduce": "배열을 하나의 값으로 누적",
    "push": "배열 끝에 원소 추가", "pop": "배열 마지막 원소 꺼내기", "slice": "배열/문자열 일부 자르기",
    "printf": "서식 문자열을 콘솔에 출력", "sprintf": "서식 문자열을 버퍼에 저장", "fprintf": "파일/스트림에 출력",
    "malloc": "동적 메모리 할당", "calloc": "0으로 초기화된 동적 메모리 할당", "free": "동적 메모리 해제",
    "memcpy": "메모리 블록 복사", "memset": "메모리 블록을 특정 값으로 채움", "sizeof": "자료형/변수 바이트 크기",
    "std::cout": "표준 출력 스트림", "std::vector": "가변 크기 동적 배열", "push_back": "벡터 끝에 원소 추가",
    "size": "컨테이너 원소 개수", "empty": "비어 있는지 검사", "find": "원소/부분 문자열 검색",
    "zeros": "0으로 채운 행렬/배열 생성", "ones": "1로 채운 행렬/배열 생성", "eye": "단위 행렬 생성",
    "linspace": "구간 균등 분할 벡터 생성", "reshape": "행렬 차원/모양 변경", "disp": "콘솔에 값 표시",
    "length": "벡터의 최대 차원 길이", "numel": "배열 전체 원소 개수", "plot": "2D 그래프 그리기",
    "figure": "새 그래프 창 생성", "subplot": "화면을 격자로 나눠 그래프 배치", "fft": "고속 푸리에 변환(FFT)",
    "ifft": "역 FFT", "mean": "평균값 계산", "sum": "합계 계산", "abs": "절댓값/복소수 크기",
    "sqrt": "제곱근", "load": "MAT/데이터 파일 불러오기", "save": "변수를 MAT 파일로 저장",
    "error": "오류 발생 및 중단", "warning": "경고 메시지 출력", "nargin": "전달된 입력 인자 개수",
}

# ───────────────────────────── 지식 베이스 (결정적 해설용) ─────────────────────────────
_KB_RAW = """
len|길이(원소 개수)를 반환
range|연속된 정수 시퀀스 생성 (반복문에서 자주 사용)
enumerate|(번호, 값) 쌍으로 순회하게 만듦
zip|여러 시퀀스를 같은 위치끼리 묶음
sorted|정렬된 새 리스트를 반환 (원본은 유지)
reversed|뒤집힌 순서로 순회
sum|합계를 계산
min|최솟값
max|최댓값
abs|절댓값 (복소수면 크기)
round|반올림
any|하나라도 참이면 True
all|모두 참이면 True
map|각 원소에 함수를 적용
filter|조건을 만족하는 원소만 남김
isinstance|객체가 특정 타입인지 검사
getattr|이름으로 속성 값을 가져옴
setattr|이름으로 속성 값을 설정
hasattr|속성이 존재하는지 검사
print|화면(콘솔)에 출력
open|파일 열기
input|사용자 입력 받기
str|문자열로 변환/생성
int|정수로 변환/생성
float|실수로 변환/생성
bool|불리언으로 변환
list|리스트 생성/변환
dict|딕셔너리 생성/변환
set|집합 생성/변환 (중복 제거)
tuple|튜플 생성/변환
super|부모 클래스 접근
type|객체의 타입 반환
repr|개발자용 문자열 표현
iter|이터레이터 생성
next|이터레이터의 다음 값
divmod|(몫, 나머지) 반환
pow|거듭제곱
os.path.join|경로 조각들을 OS에 맞게 결합
os.path.exists|경로 존재 여부
os.path.isfile|파일인지 검사
os.path.isdir|폴더인지 검사
os.path.dirname|경로에서 폴더 부분 추출
os.path.basename|경로에서 파일명 추출
os.path.abspath|절대 경로로 변환
os.walk|폴더를 재귀적으로 순회
os.getenv|환경 변수 읽기
os.makedirs|폴더 생성(중간 폴더 포함)
os.listdir|폴더 안의 항목 목록
os.remove|파일 삭제
sys.exit|프로그램 종료
json.loads|JSON 문자열 → 파이썬 객체
json.dumps|파이썬 객체 → JSON 문자열
json.load|JSON 파일 → 파이썬 객체
json.dump|파이썬 객체 → JSON 파일
re.sub|정규식으로 치환
re.match|문자열 시작부터 정규식 매칭
re.search|문자열 안에서 정규식 검색
re.findall|정규식에 맞는 모든 부분 반환
re.compile|정규식 미리 컴파일
re.split|정규식으로 분할
time.time|현재 시각(초)
time.sleep|지정한 시간 동안 대기
time.perf_counter|고해상도 시간 측정
math.sqrt|제곱근
math.sin|사인
math.cos|코사인
math.atan2|atan2(y, x) 각도
math.pi|원주율
math.log|로그
math.exp|지수함수
random.random|0~1 난수
random.randint|정수 난수
random.choice|무작위 선택
random.shuffle|무작위 섞기
collections.defaultdict|기본값이 자동 생성되는 딕셔너리
collections.Counter|개수 세기 딕셔너리
collections.deque|양방향 큐
itertools.product|데카르트 곱
functools.lru_cache|결과 캐싱 데코레이터
pathlib.Path|경로 객체 생성
dataclasses.dataclass|데이터 보관용 클래스 자동 생성 데코레이터
dataclasses.field|데이터클래스 필드 설정
dataclasses.asdict|데이터클래스 → 딕셔너리
threading.Thread|별도 스레드 생성
threading.Lock|스레드 잠금 객체
subprocess.run|외부 프로그램 실행
argparse.ArgumentParser|명령행 인자 파서 생성
logging.getLogger|로거 가져오기
datetime.datetime.now|현재 날짜·시각
urllib.request.urlopen|URL 요청 보내기(HTTP)
urllib.request.Request|HTTP 요청 객체 생성
webbrowser.open|기본 웹브라우저로 열기
ast.parse|파이썬 소스를 AST로 파싱
ast.walk|AST 노드를 모두 순회
ast.unparse|AST를 소스 문자열로 복원
tokenize.generate_tokens|소스를 토큰으로 분해
hashlib.sha1|SHA-1 해시 객체
hashlib.sha256|SHA-256 해시 객체
tkinter.Tk|GUI 메인 창 생성
tkinter.Frame|GUI 프레임(컨테이너)
tkinter.Button|GUI 버튼
tkinter.Label|GUI 라벨
tkinter.Entry|GUI 입력창
pickle.load|파일에서 객체 복원
pickle.dump|객체를 파일에 저장
shutil.copy|파일 복사
shutil.rmtree|폴더 통째로 삭제
numpy.array|리스트 등을 ndarray로 변환
numpy.zeros|0으로 채운 배열
numpy.ones|1로 채운 배열
numpy.empty|초기화 없이 배열 할당
numpy.arange|등차 수열 배열
numpy.linspace|구간을 균등 분할한 배열
numpy.abs|절댓값(복소수는 크기)
numpy.angle|복소수의 위상(라디안)
numpy.conj|켤레복소수
numpy.real|실수부
numpy.imag|허수부
numpy.exp|지수함수
numpy.log|자연로그
numpy.log10|상용로그
numpy.sqrt|제곱근
numpy.sin|사인
numpy.cos|코사인
numpy.arctan2|atan2(y, x) 각도
numpy.sum|합
numpy.mean|평균
numpy.std|표준편차
numpy.var|분산
numpy.max|최댓값
numpy.min|최솟값
numpy.argmax|최댓값의 인덱스
numpy.argmin|최솟값의 인덱스
numpy.dot|내적/행렬곱
numpy.matmul|행렬곱
numpy.outer|외적(벡터→행렬)
numpy.reshape|배열 모양 변경
numpy.concatenate|배열 이어붙이기
numpy.stack|새 축으로 쌓기
numpy.where|조건에 따라 선택/위치 반환
numpy.clip|값 범위 제한
numpy.cumsum|누적합
numpy.diff|인접 원소 차분
numpy.sort|정렬
numpy.argsort|정렬 순서 인덱스
numpy.unique|중복 제거
numpy.convolve|1차원 합성곱
numpy.deg2rad|도→라디안
numpy.rad2deg|라디안→도
numpy.fft.fft|이산 푸리에 변환(FFT)
numpy.fft.ifft|역 FFT
numpy.fft.fftshift|주파수 0을 중앙으로 이동
numpy.fft.fftfreq|FFT 주파수 축 생성
numpy.linalg.norm|벡터/행렬 노름(크기)
numpy.linalg.inv|역행렬
numpy.linalg.solve|선형방정식 풀이
numpy.linalg.eig|고유값·고유벡터
numpy.random.randn|표준정규분포 난수
numpy.random.rand|0~1 균등 난수
numpy.random.normal|정규분포 난수
numpy.save|배열을 .npy 로 저장
numpy.load|.npy 배열 불러오기
numpy.hstack|가로로 이어붙이기
numpy.vstack|세로로 이어붙이기
numpy.meshgrid|격자 좌표 생성
numpy.isnan|NaN 여부
numpy.allclose|거의 같은지 비교
scipy.signal.convolve|신호 합성곱
scipy.signal.butter|버터워스 필터 설계
scipy.signal.lfilter|IIR/FIR 필터 적용
scipy.signal.find_peaks|피크 검출
scipy.optimize.minimize|함수 최소화
scipy.optimize.least_squares|비선형 최소제곱
scipy.linalg.inv|역행렬
torch.tensor|텐서 생성
torch.zeros|0 텐서
torch.cat|텐서 이어붙이기
torch.no_grad|기울기 계산 비활성화 컨텍스트
torch.save|모델/텐서 저장
torch.load|모델/텐서 불러오기
torch.nn.Module|신경망 모듈 기본 클래스
torch.nn.Linear|완전연결 층
torch.nn.Conv2d|2D 합성곱 층
torch.nn.ReLU|ReLU 활성화
torch.softmax|소프트맥스
matplotlib.pyplot.plot|선 그래프
matplotlib.pyplot.figure|새 그림 생성
matplotlib.pyplot.show|그림 화면에 표시
matplotlib.pyplot.subplots|그림과 축 한 번에 생성
matplotlib.pyplot.savefig|그림 파일로 저장
matplotlib.pyplot.imshow|2D 배열을 이미지로 표시
h5py.File|HDF5 파일 열기
pandas.read_csv|CSV → DataFrame
pandas.DataFrame|표 형태 데이터 생성
"""
KB_CALLS: Dict[str, str] = dict(
    ln.split("|", 1) for ln in _KB_RAW.strip().splitlines() if "|" in ln
)

_KBM_RAW = """
append|(리스트 등) 끝에 원소 추가
extend|(리스트 등) 여러 원소를 이어 붙임
insert|(리스트 등) 지정 위치에 삽입
pop|마지막(또는 지정) 원소를 꺼내 제거
remove|값과 일치하는 첫 원소 제거
clear|내용을 모두 비움
sort|제자리 정렬
reverse|제자리 뒤집기
copy|얕은 복사본 생성
get|(딕셔너리) 키로 값 조회, 없으면 기본값
items|(딕셔너리) (키, 값) 쌍 목록
keys|(딕셔너리) 키 목록
values|(딕셔너리) 값 목록
update|(딕셔너리/집합) 다른 내용으로 갱신
setdefault|(딕셔너리) 키가 없으면 기본값을 넣고 반환
add|(집합) 원소 추가
discard|(집합) 원소 제거(없어도 오류 없음)
join|(문자열) 구분자로 문자열들을 이어붙임
split|(문자열) 구분자로 분리
rsplit|(문자열) 오른쪽부터 분리
strip|(문자열) 양끝 공백/문자 제거
lstrip|(문자열) 왼쪽 공백 제거
rstrip|(문자열) 오른쪽 공백 제거
replace|(문자열) 일부를 치환
startswith|(문자열) 특정 문자열로 시작하는지
endswith|(문자열) 특정 문자열로 끝나는지
format|(문자열) 자리표시자에 값 채우기
lower|(문자열) 소문자로
upper|(문자열) 대문자로
find|(문자열) 부분 문자열 위치 찾기
encode|(문자열) 바이트로 인코딩
decode|(바이트) 문자열로 디코딩
read|(파일) 내용 읽기
write|(파일) 내용 쓰기
readlines|(파일) 줄 단위 목록으로 읽기
close|(파일/자원) 닫기
read_text|(Path) 텍스트 파일 읽기
write_text|(Path) 텍스트 파일 쓰기
is_file|(Path) 파일인지 검사
is_dir|(Path) 폴더인지 검사
exists|(Path) 존재 여부
mkdir|(Path) 폴더 생성
resolve|(Path) 절대 경로로 정규화
relative_to|(Path) 기준 경로에 대한 상대 경로
with_suffix|(Path) 확장자 변경
glob|(Path) 패턴에 맞는 파일 찾기
rglob|(Path) 하위 폴더까지 패턴 검색
reshape|(배열) 모양 변경
astype|(배열) 자료형 변환
mean|(배열) 평균
sum|(배열) 합
max|(배열) 최댓값
min|(배열) 최솟값
flatten|(배열) 1차원으로 펴기
tolist|(배열) 파이썬 리스트로 변환
transpose|(배열) 축 바꾸기(전치)
conj|(배열) 켤레복소수
group|(정규식 매치) 캡처 그룹 문자열
sub|(정규식) 치환
match|(정규식) 시작부터 매칭
search|(정규식) 검색
findall|(정규식) 모든 매치
bind|(GUI) 이벤트 연결
pack|(GUI) 위젯 배치
grid|(GUI) 격자 배치
configure|(GUI) 위젯 설정 변경
after|(GUI) 일정 시간 뒤 콜백 실행
mainloop|(GUI) 이벤트 루프 시작
destroy|(GUI) 창 닫기
start|스레드/작업 시작
put|(큐) 항목 넣기
acquire|(락) 잠금 획득
release|(락) 잠금 해제
submit|(실행기) 작업 제출
result|(Future) 결과 대기·반환
hexdigest|(해시) 16진수 문자열 결과
update_status|상태 갱신
to|(텐서) 장치/자료형 이동
item|(텐서) 파이썬 숫자로 변환
detach|(텐서) 계산 그래프에서 분리
backward|(텐서) 역전파 수행
step|(옵티마이저) 파라미터 한 스텝 갱신
zero_grad|(옵티마이저) 기울기 초기화
"""
KB_METHODS: Dict[str, str] = dict(
    ln.split("|", 1) for ln in _KBM_RAW.strip().splitlines() if "|" in ln
)
GUESS_BLOCK = set(KB_METHODS) | {
    "run", "main", "start", "stop", "load", "save", "set", "reset", "forward", "call",
    "process", "handle", "execute", "build", "create", "init", "open", "send", "recv",
    "show", "hide", "draw", "render", "clone", "dump", "parse", "name", "size", "next",
}
MUTATORS = {"append", "extend", "insert", "pop", "remove", "clear", "update", "add",
            "discard", "sort", "reverse", "setdefault", "put", "write", "push", "appendleft"}
DECORATOR_KB = {
    "staticmethod": "인스턴스 없이 호출되는 정적 메서드",
    "classmethod": "클래스를 첫 인자(cls)로 받는 메서드",
    "property": "메서드를 속성처럼 읽게 해주는 프로퍼티",
    "dataclass": "데이터 보관용 클래스(__init__ 등 자동 생성)",
    "lru_cache": "호출 결과를 캐싱",
    "cache": "호출 결과를 캐싱",
    "contextmanager": "with 문에서 쓸 수 있는 컨텍스트 매니저로 변환",
    "abstractmethod": "자식 클래스가 반드시 구현해야 하는 추상 메서드",
    "wraps": "래퍼 함수가 원본 메타정보를 유지하게 함",
    "overload": "타입 힌트용 오버로드 선언",
}
EFFECT_LABELS = {
    "file": "파일 I/O", "net": "네트워크", "proc": "외부 프로세스", "gui": "GUI",
    "out": "콘솔/로그 출력", "thread": "스레드/병렬", "sleep": "대기(sleep)",
    "rand": "난수", "glob": "전역 상태 변경",
}
_FILE_LAST = {"read_text", "write_text", "read_bytes", "write_bytes", "unlink", "mkdir",
              "rmdir", "readlines", "readline", "touch", "rename", "iterdir", "glob", "rglob"}
_FILE_PREFIX = ("open", "io.open", "os.remove", "os.rename", "os.makedirs", "os.mkdir",
                "os.unlink", "shutil.", "h5py.", "numpy.save", "numpy.load", "pickle.",
                "json.dump", "json.load", "torch.save", "torch.load", "pandas.read",
                "csv.", "os.listdir", "os.walk")


def effect_of(canon: str, last: str) -> Optional[str]:
    if canon.startswith(("urllib", "requests", "socket", "http", "aiohttp", "websocket")):
        return "net"
    if canon.startswith(("subprocess", "os.system", "os.popen")):
        return "proc"
    if canon.startswith(("tkinter", "PyQt", "matplotlib.pyplot.show")):
        return "gui"
    if canon in ("print",) or canon.startswith(("logging", "sys.stdout", "sys.stderr")):
        return "out"
    if canon.startswith(("threading", "multiprocessing", "asyncio", "concurrent")):
        return "thread"
    if canon == "time.sleep":
        return "sleep"
    if canon.startswith(("random.", "numpy.random")):
        return "rand"
    if canon.startswith(_FILE_PREFIX) or last in _FILE_LAST:
        return "file"
    return None


def kb_lookup(canon: str, last: str) -> str:
    if canon in KB_CALLS:
        return KB_CALLS[canon]
    if last in KB_METHODS and "." in canon:
        return "(일반적으로) " + KB_METHODS[last]
    return ""


# ───────────────────────────── 공용 유틸 ─────────────────────────────
def short(s: str, n: int = 60) -> str:
    s = " ".join(str(s).split())
    return s if len(s) <= n else s[: n - 1] + "…"


def clamp_sentences(s: str, n: int) -> str:
    s = " ".join(s.split())
    return s if len(s) <= n else s[: n - 1].rstrip() + "…"


def sha1(s: str) -> str:
    return hashlib.sha1(s.encode("utf-8", "ignore")).hexdigest()


def safe_ident(s: str) -> bool:
    return bool(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s))


# ───────────────────────────── 데이터 모델 ─────────────────────────────
class FileRec:
    def __init__(self, idx: int, rel: str, module: str, text: str, is_init: bool, lang: str = "py"):
        self.idx = idx
        self.rel = rel
        self.module = module
        self.is_init = is_init
        self.lang = lang
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        self.text = text
        lines = text.split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        self.lines: List[str] = lines
        self._bl: Optional[List[bytes]] = None
        self.tree: Optional[ast.Module] = None
        self.ts_tree: Any = None
        self.foreign_segs: Optional[List[list]] = None
        self.err: Optional[str] = None
        self.parents: Dict[int, ast.AST] = {}
        self.module_unit: Optional["Unit"] = None
        self.imports_all: set = set()
        self.deps: set = set()
        self.info: Dict[int, dict] = {}
        self.sem: Dict[Tuple[int, int], tuple] = {}
        self.comments: Dict[int, Tuple[str, bool]] = {}
        self.tokens: list = []

    def bl(self) -> List[bytes]:
        if self._bl is None:
            self._bl = [ln.encode("utf-8", "replace") for ln in self.lines]
        return self._bl

    def cc(self, lineno: int, byteoff: int) -> int:
        """AST의 UTF-8 바이트 오프셋 → 문자 오프셋."""
        if not (1 <= lineno <= len(self.lines)):
            return byteoff
        line = self.lines[lineno - 1]
        if line.isascii():
            return byteoff
        return len(self.bl()[lineno - 1][:byteoff].decode("utf-8", "ignore"))

    def seg(self, node: ast.AST) -> str:
        try:
            l1, c1 = node.lineno, node.col_offset
            l2, c2 = node.end_lineno, node.end_col_offset
            bl = self.bl()
            if l1 == l2:
                b = bl[l1 - 1][c1:c2]
            else:
                parts = [bl[l1 - 1][c1:]] + bl[l1:l2 - 1] + [bl[l2 - 1][:c2]]
                b = b" ".join(p.strip() for p in parts)
            return b.decode("utf-8", "ignore")
        except Exception:
            try:
                return ast.unparse(node)
            except Exception:
                return type(node).__name__

    def line_is_comment(self, ln: int) -> bool:
        if not (1 <= ln <= len(self.lines)):
            return False
        s = self.lines[ln - 1].strip()
        if self.lang == "py":
            return s.startswith("#")
        if self.lang == "matlab":
            return s.startswith("%")
        return s.startswith(("//", "/*", "*"))

    def line_is_blank(self, ln: int) -> bool:
        return 1 <= ln <= len(self.lines) and not self.lines[ln - 1].strip()


class Unit:
    """분석 단위: module(모듈 실행부) / class / function(메서드·중첩 함수 포함)."""

    def __init__(self, uid: int, kind: str, name: str, file: int, node: ast.AST,
                 parent: Optional["Unit"], cls: Optional["Unit"]):
        self.id = uid
        self.kind = kind
        self.name = name
        self.file = file
        self.node = node
        self.parent = parent
        self.cls = cls
        self.children: List["Unit"] = []
        self.local_defs: Dict[str, "Unit"] = {}
        self.aliases: Dict[str, tuple] = {}
        self.stmts: List[ast.AST] = []
        self.local_names: set = set()
        self.globals_declared: set = set()
        self.params: List[dict] = []
        self.self_name: Optional[str] = None
        self.doc = ""
        self.line = getattr(node, "lineno", 1)
        self.end = getattr(node, "end_lineno", self.line)
        self.disp = name
        self.qual = name
        self.vt: Optional[dict] = None
        self.vars: Dict[str, dict] = {}
        self.externals: Dict[str, dict] = {}
        self.callees: Dict[int, dict] = {}
        self.callers: Dict[int, dict] = {}
        self.effects: set = set()
        self.ext_calls: Counter = Counter()
        self.outline: List[dict] = []
        self.rets: List[str] = []
        self.ret_ann = ""
        self.cnt: Counter = Counter()
        self.depth = 0
        self.code_lines = 0
        self.metrics: Dict[str, Any] = {}
        self.static: Dict[str, Any] = {}
        self.decos: List[str] = []
        self.is_entry = False
        self.is_dead = False
        self.is_recursive = False
        self.attrs: Dict[str, dict] = {}
        self.steps: List[dict] = []
        self.lang: str = "py"
        self.ts_node: Any = None
        self.sig_str: str = ""
        self.ai: Optional[dict] = None


class Res:
    __slots__ = ("kind", "unit", "canon")

    def __init__(self, kind: str, unit: Optional[Unit] = None, canon: str = ""):
        self.kind = kind      # unit | class | ext | guess | module | none
        self.unit = unit
        self.canon = canon


NONE_RES = Res("none")


# ───────────────────────────── AST 보조 함수 ─────────────────────────────
DEF_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef)
SCOPE_TYPES = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
LOOP_TYPES = (ast.For, ast.AsyncFor, ast.While)
CHAIN_TYPES = tuple(t for t in (
    ast.If, ast.For, ast.AsyncFor, ast.While, ast.With, ast.AsyncWith, ast.Try,
    getattr(ast, "TryStar", None), ast.ExceptHandler, getattr(ast, "Match", None)) if t)
TRY_TYPES = tuple(t for t in (ast.Try, getattr(ast, "TryStar", None)) if t)


def child_stmts(n: ast.AST) -> List[ast.AST]:
    out: List[ast.AST] = []
    for fld in ("body", "orelse", "finalbody"):
        v = getattr(n, fld, None)
        if isinstance(v, list):
            out.extend(x for x in v if isinstance(x, ast.AST))
    for h in getattr(n, "handlers", None) or []:
        out.append(h)
    for c in getattr(n, "cases", None) or []:
        out.extend(c.body)
    out.sort(key=lambda x: (getattr(x, "lineno", 0), getattr(x, "col_offset", 0)))
    return out


def iter_scope_stmts(body: List[ast.AST]):
    """한 스코프에 속한 모든 문장(중첩 def/class 의 본문은 제외)을 소스 순서로 순회."""
    stack = list(reversed(body))
    while stack:
        n = stack.pop()
        yield n
        if isinstance(n, SCOPE_TYPES):
            continue
        stack.extend(reversed(child_stmts(n)))


def header_exprs(st: ast.AST) -> List[ast.AST]:
    """문장 '머리'에 해당하는 표현식(본문 블록은 제외)."""
    out: List[ast.AST] = []
    if isinstance(st, DEF_TYPES):
        out += list(st.decorator_list)
        a = st.args
        out += [d for d in a.defaults if d is not None]
        out += [d for d in a.kw_defaults if d is not None]
        for arg in a.posonlyargs + a.args + a.kwonlyargs + \
                ([a.vararg] if a.vararg else []) + ([a.kwarg] if a.kwarg else []):
            if arg.annotation is not None:
                out.append(arg.annotation)
        if st.returns is not None:
            out.append(st.returns)
    elif isinstance(st, ast.ClassDef):
        out += list(st.decorator_list) + list(st.bases) + [k.value for k in st.keywords]
    elif isinstance(st, ast.ExceptHandler):
        if st.type is not None:
            out.append(st.type)
    else:
        for fld, val in ast.iter_fields(st):
            if fld in ("body", "orelse", "finalbody", "handlers", "cases"):
                continue
            if isinstance(val, ast.AST):
                out.append(val)
            elif isinstance(val, list):
                out += [v for v in val if isinstance(v, ast.AST)]
    return out


def flatten_attr(expr: ast.AST) -> Tuple[List[str], Optional[ast.AST]]:
    parts: List[str] = []
    while isinstance(expr, ast.Attribute):
        parts.append(expr.attr)
        expr = expr.value
    if isinstance(expr, ast.Name):
        parts.append(expr.id)
        return list(reversed(parts)), None
    return list(reversed(parts)), expr


def find_kw_line(fr: FileRec, first_line: int, kw: str) -> Optional[int]:
    ln = first_line
    while ln >= 1:
        t = fr.lines[ln - 1].strip()
        if t.startswith(kw):
            return ln
        if t == "" or t.startswith("#"):
            ln -= 1
            continue
        return None
    return None


OP_NAMES = {
    ast.Add: "더해서", ast.Sub: "빼서", ast.Mult: "곱해서", ast.Div: "나눠서",
    ast.FloorDiv: "나눈 몫으로", ast.Mod: "나머지 연산으로", ast.Pow: "거듭제곱해서",
    ast.BitOr: "비트 OR(또는 합집합)으로", ast.BitAnd: "비트 AND(또는 교집합)으로",
    ast.BitXor: "비트 XOR로", ast.LShift: "왼쪽 시프트로", ast.RShift: "오른쪽 시프트로",
    ast.MatMult: "행렬곱으로",
}
OP_SYMS = {
    ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Div: "/", ast.FloorDiv: "//",
    ast.Mod: "%", ast.Pow: "**", ast.BitOr: "|", ast.BitAnd: "&", ast.BitXor: "^",
    ast.LShift: "<<", ast.RShift: ">>", ast.MatMult: "@",
}
NP_ARRAY_FUNCS = {"array", "zeros", "ones", "empty", "arange", "linspace", "abs", "exp",
                  "sqrt", "sin", "cos", "concatenate", "stack", "reshape", "hstack",
                  "vstack", "fft", "ifft", "fftshift", "conj", "angle", "real", "imag",
                  "cumsum", "diff", "clip", "sort", "where", "outer", "dot", "matmul"}
TYPE_BY_NAME = {
    "len": "int", "str": "str", "int": "int", "float": "float", "list": "list",
    "dict": "dict", "set": "set", "tuple": "tuple", "sorted": "list", "bool": "bool",
    "repr": "str", "open": "file", "range": "range", "enumerate": "enumerate",
    "zip": "zip", "sum": "number", "abs": "number", "round": "number", "min": "?",
    "max": "?", "Path": "Path", "input": "str", "bytes": "bytes",
}
TYPE_BY_METHOD = {
    "join": "str", "strip": "str", "lstrip": "str", "rstrip": "str", "replace": "str",
    "lower": "str", "upper": "str", "format": "str", "read_text": "str",
    "split": "list[str]", "splitlines": "list[str]", "keys": "dict_keys",
    "values": "dict_values", "items": "dict_items", "startswith": "bool",
    "endswith": "bool", "is_file": "bool", "is_dir": "bool", "exists": "bool",
    "copy": "copy", "encode": "bytes", "decode": "str", "hexdigest": "str",
}


# ───────────────────────────── 해석(Resolver) ─────────────────────────────
class ResolverMixin:
    files: List[FileRec]
    units: List[Unit]

    # ---- 모듈 매핑 ----
    def build_modmap(self) -> None:
        self.modmap: Dict[str, int] = {}
        suffix: Dict[str, List[int]] = defaultdict(list)
        for fr in self.files:
            self.modmap[fr.module] = fr.idx
            parts = fr.module.split(".")
            for k in range(1, len(parts)):
                suffix[".".join(parts[k:])].append(fr.idx)
        self.suffix_map = {k: v[0] for k, v in suffix.items() if len(v) == 1 and k not in self.modmap}

    def find_module(self, name: str) -> Optional[int]:
        if not name:
            return None
        if name in self.modmap:
            return self.modmap[name]
        return self.suffix_map.get(name)

    def resolve_relative(self, fr: FileRec, level: int, module: Optional[str]) -> str:
        if level == 0:
            return module or ""
        pkg = fr.module if fr.is_init else fr.module.rpartition(".")[0]
        parts = pkg.split(".") if pkg else []
        drop = level - 1
        parts = parts[: len(parts) - drop] if len(parts) >= drop else []
        base = ".".join(parts)
        return (base + "." + module).strip(".") if module else base

    # ---- 이름 해석 ----
    def alias_target(self, spec: tuple, depth: int = 0) -> tuple:
        if spec[0] == "mod":
            f = self.find_module(spec[1])
            return ("module", f) if f is not None else ("ext", spec[1])
        _, m, n = spec
        f = self.find_module((m + "." + n) if m else n)
        if f is not None:
            return ("module", f)
        fm = self.find_module(m) if m else None
        if fm is not None:
            return self.symbol_in_file(fm, n, depth)
        return ("ext", (m + "." + n) if m else n)

    def symbol_in_file(self, f: int, n: str, depth: int) -> tuple:
        mu = self.files[f].module_unit
        u = mu.local_defs.get(n)
        if u is not None:
            return ("unit", u)
        spec = mu.aliases.get(n)
        if spec is not None and depth < 4:
            t = self.alias_target(spec, depth + 1)
            if t[0] in ("unit", "module"):
                return t
        return ("ext", self.files[f].module + "." + n)

    def resolve_name(self, name: str, scope: Unit) -> Optional[tuple]:
        s: Optional[Unit] = scope
        first = True
        while s is not None:
            if s.kind != "class" or first:
                u = s.local_defs.get(name)
                if u is not None:
                    return ("unit", u)
                spec = s.aliases.get(name)
                if spec is not None:
                    return self.alias_target(spec)
                if name in s.local_names:
                    return None
            first = False
            s = s.parent
        if name in BUILTINS:
            return ("builtin", name)
        return None

    # ---- 클래스 관련 ----
    def find_method(self, c: Unit, name: str, depth: int = 0) -> Optional[Unit]:
        m = c.local_defs.get(name)
        if m is not None and m.kind == "function":
            return m
        if depth > 6:
            return None
        for b in self.class_bases.get(c.id, []):
            r = self.find_method(b, name, depth + 1)
            if r is not None:
                return r
        return None

    def attr_type(self, c: Unit, name: str, depth: int = 0) -> Optional[Unit]:
        t = self.class_attr_types.get(c.id, {}).get(name)
        if t is not None or depth > 6:
            return t
        for b in self.class_bases.get(c.id, []):
            t = self.attr_type(b, name, depth + 1)
            if t is not None:
                return t
        return None

    def ann_class(self, ann: Optional[ast.AST], scope: Unit) -> Optional[Unit]:
        if ann is None:
            return None
        if isinstance(ann, ast.Constant) and isinstance(ann.value, str):
            try:
                ann = ast.parse(ann.value, mode="eval").body
            except SyntaxError:
                return None
        if isinstance(ann, ast.Subscript):
            v = ann.value
            vn = v.id if isinstance(v, ast.Name) else (v.attr if isinstance(v, ast.Attribute) else "")
            if vn == "Optional":
                sl = ann.slice
                if sl.__class__.__name__ == "Index":
                    sl = sl.value  # type: ignore[attr-defined]
                return self.ann_class(sl, scope)
            return None
        if isinstance(ann, (ast.Name, ast.Attribute)):
            r = self.resolve_expr(ann, scope)
            if r.kind == "class":
                return r.unit
        return None

    def class_of_value(self, v: ast.AST, scope: Unit, vt: dict) -> Optional[Unit]:
        if isinstance(v, ast.Call):
            r = self.resolve_expr(v.func, scope, vt)
            if r.kind == "class":
                return r.unit
        elif isinstance(v, ast.Name):
            return vt.get(v.id)
        elif isinstance(v, ast.BoolOp):
            for x in v.values:
                c = self.class_of_value(x, scope, vt)
                if c is not None:
                    return c
        elif isinstance(v, ast.IfExp):
            return self.class_of_value(v.body, scope, vt) or self.class_of_value(v.orelse, scope, vt)
        return None

    def var_types(self, u: Unit) -> dict:
        if u.vt is not None:
            return u.vt
        vt: Dict[str, Unit] = {}
        u.vt = vt  # 재귀 방지
        for p in u.params:
            c = self.ann_class(p.get("ann_node"), u)
            if c is not None:
                vt[p["name"]] = c
        for st in u.stmts:
            try:
                if isinstance(st, ast.Assign):
                    c = self.class_of_value(st.value, u, vt)
                    if c is not None:
                        for t in st.targets:
                            if isinstance(t, ast.Name):
                                vt[t.id] = c
                elif isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name):
                    c = self.ann_class(st.annotation, u)
                    if c is None and st.value is not None:
                        c = self.class_of_value(st.value, u, vt)
                    if c is not None:
                        vt[st.target.id] = c
                elif isinstance(st, (ast.With, ast.AsyncWith)):
                    for it in st.items:
                        if isinstance(it.optional_vars, ast.Name):
                            c = self.class_of_value(it.context_expr, u, vt)
                            if c is not None:
                                vt[it.optional_vars.id] = c
            except Exception:
                continue
        return vt

    # ---- 식 해석 ----
    def guess_res(self, name: Optional[str]) -> Res:
        if not name or name in GUESS_BLOCK or name.startswith("__"):
            return NONE_RES
        cands = [c for c in self.by_short.get(name, []) if c.kind == "function" and c.cls is not None]
        if len(cands) == 1:
            return Res("guess", unit=cands[0])
        return NONE_RES

    def resolve_on_class(self, c: Unit, rest: List[str], via_self: bool = False) -> Res:
        if not rest:
            return NONE_RES
        name = rest[0]
        if len(rest) == 1:
            m = self.find_method(c, name)
            if m is not None:
                return Res("unit", unit=m)
            inner = c.local_defs.get(name)
            if inner is not None and inner.kind == "class":
                return Res("class", unit=inner)
            return self.guess_res(name) if via_self else NONE_RES
        t = self.attr_type(c, name)
        if t is not None:
            return self.resolve_on_class(t, rest[1:])
        return self.guess_res(rest[-1])

    def walk_target(self, r: tuple, rest: List[str]) -> Res:
        tag, val = r
        if tag == "unit":
            u: Unit = val
            if not rest:
                return Res("class" if u.kind == "class" else "unit", unit=u)
            if u.kind == "class":
                return self.resolve_on_class(u, rest)
            return NONE_RES
        if tag == "module":
            f = val
            i = 0
            while i < len(rest):
                mu = self.files[f].module_unit
                sym = mu.local_defs.get(rest[i])
                if sym is not None:
                    return self.walk_target(("unit", sym), rest[i + 1:])
                sub = self.find_module(self.files[f].module + "." + rest[i])
                if sub is not None:
                    f = sub
                    i += 1
                    continue
                return Res("ext", canon=self.files[f].module + "." + ".".join(rest[i:]))
            return Res("module", canon=self.files[f].module)
        if tag in ("ext", "builtin"):
            base = val
            if tag == "ext":
                for i in range(len(rest)):
                    cand = base + "." + ".".join(rest[: i + 1])
                    f = self.find_module(cand)
                    if f is not None:
                        return self.walk_target(("module", f), rest[i + 1:])
            canon = base + ("." + ".".join(rest) if rest else "")
            return Res("ext", canon=canon)
        return NONE_RES

    def resolve_expr(self, expr: ast.AST, scope: Unit, vt: Optional[dict] = None) -> Res:
        vt = vt if vt is not None else {}
        parts, base = flatten_attr(expr)
        if base is not None:
            c = self.class_of_value(base, scope, vt)
            if c is not None and len(parts) == 1:
                m = self.find_method(c, parts[0])
                if m is not None:
                    return Res("unit", unit=m)
            return self.guess_res(parts[-1] if parts else None)
        name = parts[0]
        if len(parts) > 1 and scope.self_name and name == scope.self_name and scope.cls is not None:
            return self.resolve_on_class(scope.cls, parts[1:], via_self=True)
        r = self.resolve_name(name, scope)
        if r is None:
            c = vt.get(name)
            if c is not None and len(parts) > 1:
                return self.resolve_on_class(c, parts[1:])
            if len(parts) > 1:
                return self.guess_res(parts[-1])
            return NONE_RES
        return self.walk_target(r, parts[1:])


# ───────────────────────────── 다국어(tree-sitter + MATLAB) 분석기 ─────────────────────────────
_TS_FUNC_NODES = {
    "function_declaration", "generator_function_declaration", "method_definition",
    "function_definition",
}
_TS_CLASS_NODES = {"class_declaration", "class_specifier", "struct_specifier"}
_TS_CTRL_NODES = {
    "if_statement", "for_statement", "for_in_statement", "while_statement", "do_statement",
    "try_statement", "catch_clause", "finally_clause", "switch_statement", "with_statement",
}
_TS_LEAF_STR = {"string", "template_string", "string_literal", "char_literal", "system_lib_string"}
_TS_LEAF_NUM = {"number", "number_literal"}


class ForeignMixin:
    files: List[FileRec]
    units: List[Unit]
    by_short: Dict[str, List[Unit]]

    def _raw(self, fr: FileRec) -> bytes:
        b = getattr(fr, "_raw_bytes", None)
        if b is None:
            b = fr.text.encode("utf-8", "replace")
            setattr(fr, "_raw_bytes", b)
        return b

    def _nt(self, fr: FileRec, node: Any) -> str:
        return self._raw(fr)[node.start_byte:node.end_byte].decode("utf-8", "ignore")

    def _nspan(self, node: Any) -> Tuple[int, int]:
        return node.start_point[0] + 1, max(node.start_point[0] + 1, node.end_point[0] + 1)

    def _fdoc(self, fr: FileRec, line: int) -> str:
        docs: List[str] = []
        ln = line - 1
        while ln >= 1 and len(docs) < 5:
            s = fr.lines[ln - 1].strip()
            if s.startswith(("//", "/*", "*", "/**", "%")):
                cleaned = re.sub(r"^[/\*%#\s]+|[\*/\s]+$", "", s).strip()
                if cleaned:
                    docs.insert(0, cleaned)
                ln -= 1
            elif not s:
                break
            else:
                break
        return "\n".join(docs)

    def tokenize_foreign_comments(self, fr: FileRec) -> None:
        if fr.ts_tree is not None:
            stack = [fr.ts_tree.root_node]
            while stack:
                n = stack.pop()
                if n.type == "comment":
                    ln = n.start_point[0] + 1
                    txt = re.sub(r"^[/\*\s]+|[\*/\s]+$", "", self._nt(fr, n)).strip()
                    standalone = 1 <= ln <= len(fr.lines) and fr.lines[ln - 1].strip().startswith(("//", "/*"))
                    fr.comments[ln] = (txt, standalone)
                else:
                    stack.extend(reversed(n.children))
            return
        for idx, raw in enumerate(fr.lines, start=1):
            s = raw.strip()
            if fr.lang == "matlab" and "%" in raw:
                c = raw.split("%", 1)[1].strip()
                fr.comments[idx] = (c, s.startswith("%"))
            elif s.startswith(("//", "/*")):
                fr.comments[idx] = (re.sub(r"^[/\*\s]+|[\*/\s]+$", "", s).strip(), True)

    def build_foreign_segments(self, fr: FileRec) -> List[list]:
        n = len(fr.lines)
        spans: List[list] = [[] for _ in range(n + 2)]
        kws = LANG_KWS.get(fr.lang, set())
        if fr.ts_tree is not None:
            stack = [fr.ts_tree.root_node]
            while stack:
                nd = stack.pop()
                nt = nd.type
                atomic = (nd.child_count == 0) or nt == "comment" or nt in _TS_LEAF_STR or nt in _TS_LEAF_NUM
                if not atomic:
                    stack.extend(reversed(nd.children))
                    continue
                sr, sc_b = nd.start_point[0] + 1, nd.start_point[1]
                er, ec_b = nd.end_point[0] + 1, nd.end_point[1]
                sc = fr.cc(sr, sc_b)
                ec = fr.cc(er, ec_b)
                s = self._nt(fr, nd)
                cls = ""
                if nt == "comment":
                    cls = "cmt"
                elif nt in _TS_LEAF_STR:
                    cls = "str"
                elif nt in _TS_LEAF_NUM:
                    cls = "num"
                elif nt == "type_identifier" or nt == "primitive_type":
                    cls = "cl"
                elif nt in ("this", "super"):
                    cls = "slf"
                elif s in kws or nt.startswith("#"):
                    cls = "kw"
                elif nt in ("identifier", "property_identifier", "field_identifier"):
                    par = nd.parent
                    if par is not None and par.type in ("function_declarator", "function_declaration", "method_definition"):
                        cls = "df"
                sem = fr.sem.get((sr, sc)) if nt in ("identifier", "property_identifier", "field_identifier", "type_identifier") else None
                for r in range(sr, er + 1):
                    if r > n:
                        break
                    ll = len(fr.lines[r - 1])
                    s0 = sc if r == sr else 0
                    e0 = min(ec if r == er else ll, ll)
                    if e0 > s0:
                        spans[r].append((s0, e0, cls, sem if r == sr else None))
        else:
            rx = re.compile(r'("[^"\\]*(?:\\.[^"\\]*)*"|\'[^\'\\]*(?:\\.[^\'\\]*)*\'|\b\d+(?:\.\d+)?\b|\b[A-Za-z_][A-Za-z0-9_]*\b)')
            for r in range(1, n + 1):
                line = fr.lines[r - 1]
                code_part = line
                cmt_idx = -1
                if fr.lang == "matlab" and "%" in line:
                    cmt_idx = line.find("%")
                elif fr.lang != "matlab" and "//" in line:
                    cmt_idx = line.find("//")
                if cmt_idx >= 0 and not re.search(r"""['"][^'"]*(?:%|//)""", line[:cmt_idx + 2]):
                    code_part = line[:cmt_idx]
                    spans[r].append((cmt_idx, len(line), "cmt", None))
                for m in rx.finditer(code_part):
                    s0, e0 = m.span()
                    tok = m.group(0)
                    cls = ""
                    if tok[0] in ("'", '"'):
                        cls = "str"
                    elif tok[0].isdigit():
                        cls = "num"
                    elif tok in kws:
                        cls = "kw"
                    elif tok in ("this", "self"):
                        cls = "slf"
                    sem = fr.sem.get((r, s0))
                    spans[r].append((s0, e0, cls, sem))
        out: List[list] = []
        for r in range(1, n + 1):
            line = fr.lines[r - 1]
            segs: List[list] = []
            cur = 0
            for (s0, e0, cls, sem) in sorted(spans[r], key=lambda x: (x[0], x[1])):
                if e0 <= cur:
                    continue
                if s0 < cur:
                    s0 = cur
                if s0 > cur:
                    segs.append([line[cur:s0]])
                txt = line[s0:e0]
                if sem:
                    segs.append([txt, cls] + list(sem))
                elif cls:
                    segs.append([txt, cls])
                else:
                    segs.append([txt])
                cur = e0
            if cur < len(line):
                segs.append([line[cur:]])
            out.append(segs)
        return out

    def _ts_func_info(self, fr: FileRec, nd: Any) -> Tuple[str, Optional[str], List[dict], str, str]:
        """returns (func_name, owner_class_name, params, ret_ann, sig_str)"""
        name = ""
        owner = None
        params: List[dict] = []
        ret_ann = ""
        params_node = None
        if nd.type in ("arrow_function", "function_expression"):
            par = nd.parent
            if par is not None and par.type == "variable_declarator":
                idn = par.child_by_field_name("name")
                if idn:
                    name = self._nt(fr, idn)
            elif par is not None and par.type == "pair":
                kn = par.child_by_field_name("key")
                if kn:
                    name = self._nt(fr, kn).strip("'\"")
            elif par is not None and par.type == "assignment_expression":
                ln = par.child_by_field_name("left")
                if ln:
                    name = self._nt(fr, ln).split(".")[-1]
            params_node = nd.child_by_field_name("parameters") or nd.child_by_field_name("parameter")
        elif nd.type == "function_definition":
            decl = nd.child_by_field_name("declarator")
            typ = nd.child_by_field_name("type")
            if typ:
                ret_ann = short(self._nt(fr, typ), 30)
            while decl is not None and decl.type in ("pointer_declarator", "reference_declarator"):
                decl = decl.child_by_field_name("declarator")
            if decl is not None and decl.type == "function_declarator":
                dn = decl.child_by_field_name("declarator")
                if dn is not None:
                    raw_nm = self._nt(fr, dn).strip()
                    if "::" in raw_nm:
                        parts = [p.strip() for p in raw_nm.split("::") if p.strip()]
                        owner, name = parts[-2] if len(parts) >= 2 else None, parts[-1]
                    else:
                        name = raw_nm
                params_node = decl.child_by_field_name("parameters")
        else:
            nn = nd.child_by_field_name("name")
            if nn:
                name = self._nt(fr, nn)
            params_node = nd.child_by_field_name("parameters")
            rt = nd.child_by_field_name("return_type")
            if rt:
                ret_ann = short(self._nt(fr, rt).lstrip(":").strip(), 30)

        if params_node is not None:
            if params_node.type == "identifier":
                params.append({"name": self._nt(fr, params_node), "kind": "pos", "line": params_node.start_point[0] + 1,
                               "col": params_node.start_point[1], "ann": "", "ann_node": None, "default": None})
            else:
                for ch in params_node.children:
                    if ch.type in ("(", ")", ",", "comment"):
                        continue
                    ptxt = self._nt(fr, ch).strip()
                    if not ptxt or ptxt == "void":
                        continue
                    ids = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", ptxt.split("=")[0])
                    if not ids:
                        continue
                    pname = ids[-1]
                    pann = ""
                    if fr.lang in ("c", "cpp") and len(ids) >= 2:
                        pann = short(" ".join(ids[:-1]), 24)
                    elif ":" in ptxt:
                        pann = short(ptxt.split(":", 1)[1].split("=")[0].strip(), 24)
                    pdef = short(ptxt.split("=", 1)[1].strip(), 24) if "=" in ptxt else None
                    params.append({"name": pname, "kind": "pos", "line": ch.start_point[0] + 1,
                                   "col": ch.start_point[1], "ann": pann, "ann_node": None, "default": pdef})
        ln1 = nd.start_point[0] + 1
        head_line = fr.lines[ln1 - 1].strip() if 1 <= ln1 <= len(fr.lines) else ""
        sig_str = short(head_line.rstrip("{").strip(), 90)
        return name, owner, params, ret_ann, sig_str

    def build_foreign_units(self, fr: FileRec) -> None:
        mod = Unit(len(self.units), "module", "<module>", fr.idx, fr, None, None)
        self.units.append(mod)
        mod.lang = fr.lang
        mod.disp = fr.rel
        mod.qual = f"{fr.module or fr.rel}.<module>"
        mod.line, mod.end = 1, max(1, len(fr.lines))
        mod.doc = self._fdoc(fr, 1)
        fr.module_unit = mod
        if fr.lang == "matlab":
            self._build_matlab_units(fr, mod)
        elif fr.ts_tree is not None:
            self._build_ts_units(fr, mod, fr.ts_tree.root_node, None)
        else:
            self._build_brace_fallback_units(fr, mod)

    def _add_foreign_unit(self, kind: str, name: str, fr: FileRec, tok_obj: Any, parent: Unit,
                          cls: Optional[Unit], l1: int, l2: int, params: List[dict],
                          ret_ann: str = "", sig_str: str = "", doc: str = "") -> Unit:
        u = Unit(len(self.units), kind, name, fr.idx, tok_obj, parent, cls)
        self.units.append(u)
        u.lang = fr.lang
        u.line, u.end = l1, max(l1, l2)
        u.params = params
        u.ret_ann = ret_ann
        u.sig_str = sig_str
        u.doc = doc
        chain, p = [], u
        while p is not None and p.kind != "module":
            chain.append(p.name)
            p = p.parent
        u.disp = ".".join(reversed(chain))
        u.qual = f"{fr.module}.{u.disp}"
        parent.local_defs[name] = u
        parent.children.append(u)
        self.by_short[name].append(u)
        return u

    def _build_ts_units(self, fr: FileRec, parent: Unit, node: Any, cls: Optional[Unit]) -> None:
        for ch in node.children:
            nt = ch.type
            if nt == "import_statement":
                txt = self._nt(fr, ch)
                m = re.search(r"""from\s+['"]([^'"]+)['"]|import\s+['"]([^'"]+)['"]""", txt)
                if m:
                    fr.imports_all.add(m.group(1) or m.group(2))
                continue
            if nt == "preproc_include":
                txt = self._nt(fr, ch)
                m = re.search(r'"([^"]+)"|<([^>]+)>', txt)
                if m:
                    fr.imports_all.add(m.group(1) or m.group(2))
                continue
            if nt in _TS_CLASS_NODES:
                nn = ch.child_by_field_name("name")
                has_body = ch.child_by_field_name("body") is not None or any(x.type in ("class_body", "field_declaration_list") for x in ch.children)
                if nn and has_body:
                    cname = self._nt(fr, nn)
                    l1, l2 = self._nspan(ch)
                    cu = self._add_foreign_unit("class", cname, fr, ch, parent, None, l1, l2, [], sig_str=f"class {cname}", doc=self._fdoc(fr, l1))
                    cu.ts_node = ch
                    body = ch.child_by_field_name("body") or next((x for x in ch.children if x.type in ("class_body", "field_declaration_list")), ch)
                    self._build_ts_units(fr, cu, body, cu)
                    continue
            if nt in _TS_FUNC_NODES:
                name, owner, params, ret_ann, sig_str = self._ts_func_info(fr, ch)
                if name:
                    l1, l2 = self._nspan(ch)
                    tgt_cls = cls
                    if owner and owner in parent.local_defs and parent.local_defs[owner].kind == "class":
                        tgt_cls = parent.local_defs[owner]
                    fu = self._add_foreign_unit("function", name, fr, ch, tgt_cls or parent, tgt_cls, l1, l2, params, ret_ann, sig_str, self._fdoc(fr, l1))
                    fu.ts_node = ch
                    if tgt_cls is not None:
                        fu.self_name = "this"
                    continue
            if nt in ("lexical_declaration", "variable_declaration", "export_statement", "expression_statement"):
                # Arrow/function expressions assigned to a variable
                found_fn = None
                stack = [ch]
                while stack:
                    x = stack.pop()
                    if x.type in ("arrow_function", "function_expression"):
                        found_fn = x
                        break
                    if x.type not in _TS_CLASS_NODES and x.type not in _TS_FUNC_NODES:
                        stack.extend(reversed(x.children))
                if found_fn is not None:
                    name, _, params, ret_ann, sig_str = self._ts_func_info(fr, found_fn)
                    if name:
                        l1, l2 = self._nspan(ch)
                        fu = self._add_foreign_unit("function", name, fr, ch, parent, cls, l1, l2, params, ret_ann, sig_str, self._fdoc(fr, l1))
                        fu.ts_node = found_fn
                        continue
            self._build_ts_units(fr, parent, ch, cls)

    def _build_matlab_units(self, fr: FileRec, mod: Unit) -> None:
        stack: List[Tuple[str, Optional[Unit]]] = []
        fn_re = re.compile(r"^\s*function\s+(?:(?:\[([^\]]*)\]|([A-Za-z_]\w*))\s*=\s*)?([A-Za-z_]\w*)\s*(?:\(([^)]*)\))?")
        cls_re = re.compile(r"^\s*classdef\s+(?:\([^)]*\)\s*)?([A-Za-z_]\w*)")
        blk_re = re.compile(r"^\s*(if|for|parfor|while|switch|try|methods|properties|events|enumeration)\b")
        end_re = re.compile(r"^\s*end\b")
        ln = 1
        n_lines = len(fr.lines)
        while ln <= n_lines:
            raw = fr.lines[ln - 1]
            code = raw.split("%", 1)[0].strip()
            if not code:
                ln += 1
                continue
            hdr_end = ln
            if re.match(r"^function\b", code) and code.endswith("..."):
                parts = [code[:-3].strip()]
                while hdr_end < n_lines:
                    hdr_end += 1
                    nx = fr.lines[hdr_end - 1].split("%", 1)[0].strip()
                    if nx.endswith("..."):
                        parts.append(nx[:-3].strip())
                    else:
                        parts.append(nx)
                        break
                code = " ".join(parts)
            mc = cls_re.match(code)
            if mc:
                cname = mc.group(1)
                cu = self._add_foreign_unit("class", cname, fr, ("mat_c", fr.idx, ln), mod, None, ln, ln, [], sig_str=code, doc=self._fdoc(fr, ln))
                stack.append(("classdef", cu))
                ln = hdr_end + 1
                continue
            mf = fn_re.match(code)
            if mf:
                # 스크립트/다중 함수 파일에서 end 없이 새 function이 나오면 직전 함수 닫기
                while stack and stack[-1][0] == "function":
                    _, prev_u = stack.pop()
                    if prev_u is not None:
                        prev_u.end = max(prev_u.line, ln - 1)
                outs = (mf.group(1) or mf.group(2) or "").strip()
                fname = mf.group(3)
                pstr = (mf.group(4) or "").strip()
                params = []
                for p in [x.strip() for x in pstr.split(",") if x.strip()]:
                    p_ln, p_col = ln, max(0, raw.find(p))
                    for hln in range(ln, hdr_end + 1):
                        hline = fr.lines[hln - 1].split("%", 1)[0]
                        seg_start = (hline.find("(") + 1) if (hln == ln and "(" in hline) else 0
                        pm = re.search(rf"\b{re.escape(p)}\b", hline[seg_start:])
                        if pm:
                            p_ln, p_col = hln, seg_start + pm.start()
                            break
                    params.append({"name": p, "kind": "pos", "line": p_ln, "col": p_col, "ann": "", "ann_node": None, "default": None})
                cur_cls = next((u for k, u in reversed(stack) if k == "classdef"), None)
                doc_lines = []
                dl = hdr_end + 1
                while dl <= n_lines and fr.lines[dl - 1].strip().startswith("%"):
                    doc_lines.append(fr.lines[dl - 1].strip().lstrip("%").strip())
                    dl += 1
                doc = "\n".join(doc_lines) or self._fdoc(fr, ln)
                fu = self._add_foreign_unit("function", fname, fr, ("mat_f", fr.idx, ln, hdr_end), cur_cls or mod, cur_cls, ln, n_lines, params, ret_ann=outs, sig_str=short(code, 90), doc=doc)
                out_hdr: List[Tuple[str, int, int]] = []
                for ov in [x.strip() for x in outs.split(",") if x.strip()]:
                    for hln in range(ln, hdr_end + 1):
                        hline = fr.lines[hln - 1].split("%", 1)[0]
                        eq_i = hline.find("=")
                        seg = hline[:eq_i] if eq_i >= 0 else hline
                        om = re.search(rf"\b{re.escape(ov)}\b", seg)
                        if om:
                            out_hdr.append((ov, hln, om.start()))
                            break
                fu.mat_out_vars = out_hdr  # type: ignore[attr-defined]
                fr.info[ln] = {"k": "def", "a": ln, "z": hdr_end, "d": fu.id, "u": fu.id,
                               "t": f"함수 {fname} 정의", "x": f"함수 `{fname}` 를 정의합니다."}
                for hln in range(ln + 1, hdr_end + 1):
                    fr.info[hln] = {"k": "cont", "a": ln, "z": hdr_end, "u": fu.id}
                if cur_cls is not None and params:
                    fu.self_name = params[0]["name"]
                stack.append(("function", fu))
                ln = hdr_end + 1
                continue
            if blk_re.match(code):
                stack.append(("block", None))
                ln += 1
                continue
            if end_re.match(code) and stack:
                _, u_obj = stack.pop()
                if u_obj is not None:
                    u_obj.end = ln
            ln += 1
        while stack:
            _, u_obj = stack.pop()
            if u_obj is not None:
                u_obj.end = n_lines
        if not mod.children:
            self.by_short[Path(fr.rel).stem].append(mod)

    def _build_brace_fallback_units(self, fr: FileRec, mod: Unit) -> None:
        fn_re = re.compile(r"^\s*(?:export\s+)?(?:async\s+)?function\s+([A-Za-z_]\w*)\s*\(([^)]*)\)")
        for ln, raw in enumerate(fr.lines, start=1):
            m = fn_re.match(raw)
            if m:
                fname = m.group(1)
                params = [{"name": p.strip(), "kind": "pos", "line": ln, "col": 0, "ann": "", "ann_node": None, "default": None}
                          for p in m.group(2).split(",") if p.strip()]
                self._add_foreign_unit("function", fname, fr, ("fb", fr.idx, ln), mod, None, ln, ln, params, sig_str=raw.strip())

    def resolve_foreign_deps(self) -> None:
        by_rel = {fr.rel: fr.idx for fr in self.files}
        by_stem: Dict[str, List[int]] = defaultdict(list)
        by_name: Dict[str, List[int]] = defaultdict(list)
        for fr in self.files:
            by_stem[Path(fr.rel).with_suffix("").as_posix()].append(fr.idx)
            by_stem[Path(fr.rel).stem].append(fr.idx)
            by_name[Path(fr.rel).name].append(fr.idx)
        for fr in self.files:
            if fr.lang == "py":
                continue
            parent_dir = Path(fr.rel).parent
            for imp in fr.imports_all:
                if imp.startswith("."):
                    base = (parent_dir / imp).as_posix()
                    norm = os.path.normpath(base).replace("\\", "/")
                    for cand in (norm, norm + ".js", norm + ".jsx", norm + ".ts", norm + ".tsx", norm + "/index.js", norm + "/index.ts"):
                        if cand in by_rel and by_rel[cand] != fr.idx:
                            fr.deps.add(by_rel[cand])
                            break
                elif "/" in imp or "." in imp:
                    if imp in by_rel and by_rel[imp] != fr.idx:
                        fr.deps.add(by_rel[imp])
                    elif Path(imp).name in by_name:
                        for idx in by_name[Path(imp).name]:
                            if idx != fr.idx:
                                fr.deps.add(idx)
                    else:
                        self.ext_libs[imp.split("/")[0].lstrip("@")] += 1
                else:
                    self.ext_libs[imp] += 1
            # C/C++ 같은 이름의 .h <-> .cpp 연결
            if fr.lang in ("c", "cpp"):
                stem = Path(fr.rel).with_suffix("").as_posix()
                for idx in by_stem.get(stem, []):
                    if idx != fr.idx:
                        fr.deps.add(idx)

    def _resolve_foreign_call(self, fr: FileRec, u: Unit, raw_name: str, base_obj: str = "") -> Tuple[str, int, str, str]:
        short_nm = raw_name.split(".")[-1].split("::")[-1]
        if base_obj in ("this", "self") and u.cls is not None:
            m = u.cls.local_defs.get(short_nm)
            if m:
                return "u", m.id, self.unit_tip(m), short_nm
        mu = fr.module_unit
        if mu and short_nm in mu.local_defs:
            tgt = mu.local_defs[short_nm]
            return ("k" if tgt.kind == "class" else "u"), tgt.id, self.unit_tip(tgt), short_nm
        for dep_id in fr.deps:
            dmu = self.files[dep_id].module_unit
            if dmu and short_nm in dmu.local_defs:
                tgt = dmu.local_defs[short_nm]
                return ("k" if tgt.kind == "class" else "u"), tgt.id, self.unit_tip(tgt), short_nm
        cands = [x for x in self.by_short.get(short_nm, []) if x.file != fr.idx and x.kind in ("function", "module")]
        if len(cands) == 1:
            tgt = cands[0]
            if fr.lang == "matlab":
                return ("k" if tgt.kind == "class" else "u"), tgt.id, self.unit_tip(tgt), short_nm
            return "g", tgt.id, "(추정) " + self.unit_tip(tgt), short_nm
        kb = KB_FOREIGN.get(raw_name) or KB_FOREIGN.get(short_nm) or KB_CALLS.get(short_nm, "")
        if kb:
            return "e", -1, kb, raw_name
        return "?", -1, "", raw_name

    def analyze_foreign_scope(self, u: Unit) -> None:
        fr = self.files[u.file]
        for p in u.params:
            self.add_def(u, p["name"], p["line"], "(매개변수)" + (f" 기본값 {p['default']}" if p["default"] else ""), p["ann"], kind="param")
            if p["name"] != u.self_name:
                fr.sem.setdefault((p["line"], fr.cc(p["line"], p["col"])), ("v", p["name"]))
        for ov, oln, ocol in getattr(u, "mat_out_vars", []):
            self.var(u, ov, kind="local")
            fr.sem.setdefault((oln, fr.cc(oln, ocol)), ("v", ov))
        kws = LANG_KWS.get(fr.lang, set())
        if u.ts_node is not None or (u.kind == "module" and fr.ts_tree is not None):
            root = u.ts_node if u.ts_node is not None else fr.ts_tree.root_node
            self._walk_ts_scope(fr, u, root, [], kws)
        elif fr.lang == "matlab":
            self._walk_matlab_scope(fr, u, kws)
        self.compute_foreign_steps(u)

    def _walk_ts_scope(self, fr: FileRec, u: Unit, node: Any, chain: List[list], kws: set) -> None:
        body = node
        if node.type in _TS_FUNC_NODES or node.type in ("arrow_function", "function_expression"):
            body = node.child_by_field_name("body") or next((x for x in node.children if x.type in ("statement_block", "compound_statement")), node)
        elif node.type in _TS_CLASS_NODES:
            return
        children = body.children if body is not None else []
        for ch in children:
            nt = ch.type
            if nt in ("{", "}", ";", "comment") or nt in _TS_CLASS_NODES or nt in _TS_FUNC_NODES:
                continue
            if nt in ("lexical_declaration", "variable_declaration", "export_statement") and any(
                x.type in ("arrow_function", "function_expression") for x in ch.children for x in ([x] + list(x.children))
            ):
                continue
            l1, l2 = self._nspan(ch)
            if nt in _TS_CTRL_NODES:
                kind = {"if_statement": "if", "for_statement": "for", "for_in_statement": "for",
                        "while_statement": "while", "do_statement": "while", "try_statement": "try",
                        "catch_clause": "except", "finally_clause": "finally", "switch_statement": "match",
                        "with_statement": "with"}.get(nt, "stmt")
                if kind in ("if", "for", "while", "try", "match", "with"):
                    u.cnt[{"if": "if", "for": "for", "while": "while", "try": "try"}.get(kind, "if")] += 1
                elif kind == "except":
                    u.cnt["except"] += 1
                u.depth = max(u.depth, len(chain) + 1)
                head_txt = short(fr.lines[l1 - 1].strip(), 64) if 1 <= l1 <= len(fr.lines) else nt
                desc = f"`{head_txt}` 제어문을 실행합니다."
                if kind == "if":
                    desc = f"조건문 `{head_txt}` 이(가) 참일 때 블록을 실행합니다."
                elif kind in ("for", "while"):
                    desc = f"반복문 `{head_txt}` 으로 조건이 맞는 동안 블록을 반복합니다."
                elif kind == "try":
                    desc = "오류가 발생할 수 있는 `try` 블록을 시작합니다."
                elif kind == "except":
                    desc = "발생한 예외를 `catch` 로 받아 처리합니다."
                fr.info[l1] = {"k": kind, "a": l1, "z": l1, "t": kind, "x": desc, "u": u.id, "p": list(chain)}
                if u.kind != "class" and len(u.outline) < 120:
                    u.outline.append({"l": l1, "d": len(chain), "k": kind, "t": head_txt})
                # 헤더 내 호출/변수 수집
                self._extract_ts_expr_info(fr, u, ch, l1, kws, shallow=True)
                sub_chain = chain + [[l1, ""]]
                for sub in ch.children:
                    if sub.type in ("statement_block", "compound_statement", "switch_body"):
                        self._walk_ts_scope(fr, u, sub, sub_chain, kws)
                    elif sub.type in ("else_clause", "catch_clause", "finally_clause"):
                        self._walk_ts_scope(fr, u, sub, chain, kws)
                continue
            if nt == "else_clause":
                fr.info[l1] = {"k": "else", "a": l1, "z": l1, "t": "else", "x": "앞선 조건이 거짓일 때 실행되는 `else` 분기입니다.", "u": u.id, "p": list(chain)}
                for sub in ch.children:
                    if sub.type == "if_statement":
                        self._walk_ts_scope(fr, u, sub, chain, kws)
                    elif sub.type in ("statement_block", "compound_statement"):
                        self._walk_ts_scope(fr, u, sub, chain + [[l1, "e"]], kws)
                continue
            # 일반 문장
            kind = "stmt"
            if nt == "return_statement":
                kind = "return"
                u.cnt["return"] += 1
                rv = short(self._nt(fr, ch).replace("return", "", 1).rstrip(";").strip(), 36) or "void"
                if rv not in u.rets:
                    u.rets.append(rv)
            elif nt == "throw_statement":
                kind = "raise"
                u.cnt["raise"] += 1
            elif nt in ("import_statement", "preproc_include"):
                kind = "import"
            elif nt in ("lexical_declaration", "variable_declaration", "declaration"):
                kind = "assign"
            elif "call_expression" in self._nt(fr, ch) or nt == "expression_statement":
                txt_c = self._nt(fr, ch).strip()
                kind = "assign" if ("=" in txt_c.split("(")[0] and "==" not in txt_c) else "callstmt"
            reads, writes, calls = self._extract_ts_expr_info(fr, u, ch, l1, kws, shallow=False)
            head_txt = short(fr.lines[l1 - 1].strip(), 68) if 1 <= l1 <= len(fr.lines) else ""
            if kind == "return":
                desc = f"`{head_txt}` — 결과를 반환하고 함수를 마칩니다."
            elif kind == "assign":
                desc = f"`{', '.join(writes[:3]) or '변수'}` 에 값을 계산해 저장합니다 (`{head_txt}`)."
            elif calls:
                desc = f"`{calls[0][0]}` 호출을 실행합니다" + (f" ({calls[0][3]})" if calls[0][3] else "") + "."
            else:
                desc = f"`{head_txt}` 문장을 실행합니다."
            rec: Dict[str, Any] = {"k": kind, "a": l1, "z": l2, "t": kind, "x": desc, "u": u.id, "p": list(chain)}
            if reads:
                rec["r"] = reads[:8]
            if writes:
                rec["w"] = writes[:8]
            if calls:
                rec["c"] = [[c[0], c[1], c[2], short(c[3], 90)] for c in calls[:8]]
            fr.info[l1] = rec
            for ln2 in range(l1 + 1, l2 + 1):
                fr.info.setdefault(ln2, {"k": "cont", "a": l1, "z": l2, "u": u.id})
            if kind in ("return", "raise") or any(c[2] in ("u", "k") for c in calls):
                if u.kind != "class" and len(u.outline) < 120:
                    u.outline.append({"l": l1, "d": len(chain), "k": kind, "t": head_txt})

    def _extract_ts_expr_info(self, fr: FileRec, u: Unit, node: Any, stmt_line: int, kws: set, shallow: bool) -> Tuple[List[str], List[str], List[list]]:
        reads: List[str] = []
        writes: List[str] = []
        calls: List[list] = []
        seen_c: set = set()
        stack = [node]
        while stack:
            nd = stack.pop()
            nt = nd.type
            if shallow and nd is not node and nt in ("statement_block", "compound_statement", "else_clause"):
                continue
            if nt in ("call_expression", "new_expression"):
                fn_node = nd.child_by_field_name("function") or nd.child_by_field_name("constructor") or (nd.children[0] if nd.children else None)
                if fn_node is not None:
                    raw_fn = self._nt(fr, fn_node).strip()
                    base_obj = ""
                    if fn_node.type in ("member_expression", "field_expression"):
                        obj = fn_node.child_by_field_name("object") or fn_node.child_by_field_name("argument")
                        prop = fn_node.child_by_field_name("property") or fn_node.child_by_field_name("field")
                        if obj:
                            base_obj = self._nt(fr, obj).strip()
                        mark_nd = prop or fn_node
                    else:
                        mark_nd = fn_node
                    ln_c = mark_nd.start_point[0] + 1
                    col_c = fr.cc(ln_c, mark_nd.start_point[1])
                    q, tid, mean, lab = self._resolve_foreign_call(fr, u, raw_fn, base_obj)
                    if tid >= 0:
                        edge_k = "guess" if q == "g" else "call"
                        self.add_edge(u, self.units[tid], edge_k, ln_c)
                        fr.sem[(ln_c, col_c)] = ("c", tid, q, mean)
                    elif mean:
                        fr.sem[(ln_c, col_c)] = ("e", mean)
                        u.ext_calls[lab] += 1
                    u.cnt["calls"] += 1
                    if lab not in seen_c:
                        seen_c.add(lab)
                        calls.append([lab + "()", tid, q, mean])
            elif nt in ("variable_declarator", "init_declarator"):
                lhs = nd.child_by_field_name("name") or nd.child_by_field_name("declarator")
                if lhs:
                    for vname in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", self._nt(fr, lhs))[-1:]:
                        if vname not in kws:
                            self.add_def(u, vname, nd.start_point[0] + 1, self._nt(fr, nd), kind="local")
                            if vname not in writes:
                                writes.append(vname)
            elif nt == "assignment_expression":
                lhs = nd.child_by_field_name("left")
                if lhs:
                    vname = self._nt(fr, lhs).strip()
                    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", vname) and vname not in kws:
                        self.add_def(u, vname, nd.start_point[0] + 1, self._nt(fr, nd), kind="local")
                        if vname not in writes:
                            writes.append(vname)
            elif nt == "identifier":
                nm = self._nt(fr, nd)
                if nm not in kws and nm != u.self_name:
                    par = nd.parent
                    in_call_fn = par is not None and (
                        (par.type == "call_expression" and par.child_by_field_name("function") is nd) or
                        (par.type in ("member_expression", "field_expression") and par.parent is not None and par.parent.type == "call_expression")
                    )
                    if not in_call_fn and nm in u.vars:
                        ln_v = nd.start_point[0] + 1
                        col_v = fr.cc(ln_v, nd.start_point[1])
                        self.add_use(u, nm, ln_v)
                        fr.sem.setdefault((ln_v, col_v), ("v", nm))
                        if nm not in reads:
                            reads.append(nm)
            stack.extend(reversed(nd.children))
        return reads, writes, calls

    def _walk_matlab_scope(self, fr: FileRec, u: Unit, kws: set) -> None:
        chain: List[list] = []
        call_rx = re.compile(r"(?<!@)\b([A-Za-z_]\w*)\s*\(")
        ref_rx = re.compile(r"@([A-Za-z_]\w*)")
        assign_rx = re.compile(r"^\s*(?:\[([^\]]+)\]|([A-Za-z_]\w*(?:\([^)]*\))?))\s*=\s*(.+)$")
        hdr_end = u.node[3] if isinstance(u.node, tuple) and len(u.node) >= 4 else u.line
        skip_lines: set = set()
        for ch in u.children:
            for ln in range(ch.line, ch.end + 1):
                skip_lines.add(ln)
        for ln in range(u.line, u.end + 1):
            if ln in skip_lines or (u.kind == "function" and ln <= hdr_end):
                continue
            raw = fr.lines[ln - 1]
            raw_code = raw.split("%", 1)[0]
            code_nostr = re.sub(r"'[^']*'", lambda m: " " * len(m.group(0)), raw_code)
            code = raw_code.strip().rstrip(";")
            if not code:
                continue
            low = code.split()[0] if code.split() else ""
            if low == "end":
                if chain:
                    chain.pop()
                continue
            if low == "global":
                gvars = re.findall(r"\b([A-Za-z_]\w*)\b", code[6:])
                for gv in gvars:
                    if gv not in kws:
                        u.globals_declared.add(gv)
                        self.add_def(u, gv, ln, "global " + gv, kind="global")
                        col_g = code_nostr.find(gv)
                        if col_g >= 0:
                            fr.sem.setdefault((ln, col_g), ("v", gv))
                fr.info[ln] = {"k": "global", "a": ln, "z": ln, "t": "global", "x": f"전역 변수 `{', '.join(gvars)}` 를 이 스코프에서 공유합니다.", "u": u.id, "p": list(chain), "w": gvars[:8]}
                continue
            if low in ("else", "elseif", "catch", "otherwise"):
                if chain:
                    chain.pop()
                kind = "elif" if low == "elseif" else ("except" if low == "catch" else "else")
                fr.info[ln] = {"k": kind, "a": ln, "z": ln, "t": low, "x": f"`{code}` 분기를 실행합니다.", "u": u.id, "p": list(chain)}
                chain.append([ln, "e" if low == "else" else ""])
                continue
            if low in ("if", "for", "parfor", "while", "switch", "try"):
                kind = "for" if low in ("for", "parfor") else ("match" if low == "switch" else low)
                if kind in ("if", "for", "while", "try"):
                    u.cnt[kind] += 1
                u.depth = max(u.depth, len(chain) + 1)
                for wm in re.finditer(r"^\s*(?:for|parfor)\s+([A-Za-z_]\w*)\s*=", code_nostr):
                    self.add_def(u, wm.group(1), ln, code, kind="local")
                    fr.sem.setdefault((ln, wm.start(1)), ("v", wm.group(1)))
                for idm in re.finditer(r"\b([A-Za-z_]\w*)\b", code_nostr):
                    nm = idm.group(1)
                    if nm in u.vars:
                        self.add_use(u, nm, ln)
                        fr.sem.setdefault((ln, idm.start(1)), ("v", nm))
                fr.info[ln] = {"k": kind, "a": ln, "z": ln, "t": low, "x": f"`{short(code, 60)}` 제어문을 실행합니다.", "u": u.id, "p": list(chain)}
                if len(u.outline) < 120:
                    u.outline.append({"l": ln, "d": len(chain), "k": kind, "t": short(code, 72)})
                chain.append([ln, ""])
                continue
            reads: List[str] = []
            writes: List[str] = []
            calls: List[list] = []
            seen_call: set = set()
            ma = assign_rx.match(code)
            kind = "stmt"
            if ma:
                kind = "assign"
                lhs_str = ma.group(1) or ma.group(2) or ""
                lhs_base = lhs_str.split("(")[0].split(".")[0] if "(" in lhs_str and "[" not in lhs_str else lhs_str
                for w in re.findall(r"\b[A-Za-z_]\w*", re.sub(r"\([^)]*\)", "", lhs_base)):
                    if w not in kws:
                        self.add_def(u, w, ln, ma.group(3), kind="local")
                        if w not in writes:
                            writes.append(w)
                        eq_pos = code_nostr.find("=")
                        col_w = code_nostr.find(w, 0, eq_pos if eq_pos >= 0 else len(code_nostr))
                        if col_w >= 0:
                            fr.sem.setdefault((ln, col_w), ("v", w))
            elif low == "return":
                kind = "return"
                u.cnt["return"] += 1
            for rm in ref_rx.finditer(code_nostr):
                rname = rm.group(1)
                if rname in kws:
                    continue
                q, tid, mean, lab = self._resolve_foreign_call(fr, u, rname)
                if tid >= 0:
                    self.add_edge(u, self.units[tid], "ref", ln)
                    fr.sem[(ln, rm.start(1))] = ("r", tid, mean)
                    if lab not in seen_call:
                        seen_call.add(lab)
                        calls.append(["@" + lab, tid, "r", mean])
            bare_m = re.fullmatch(r"([A-Za-z_]\w*)", code)
            if bare_m and bare_m.group(1) not in kws and bare_m.group(1) not in u.vars:
                bname = bare_m.group(1)
                q, tid, mean, lab = self._resolve_foreign_call(fr, u, bname)
                if tid >= 0 or mean:
                    col_b = code_nostr.find(bname)
                    if tid >= 0:
                        self.add_edge(u, self.units[tid], "guess" if q == "g" else "call", ln)
                        if col_b >= 0:
                            fr.sem[(ln, col_b)] = ("c", tid, q, mean)
                    elif col_b >= 0:
                        fr.sem[(ln, col_b)] = ("e", mean)
                        u.ext_calls[lab] += 1
                    u.cnt["calls"] += 1
                    seen_call.add(lab)
                    calls.append([lab, tid, q, mean])
            for cm in call_rx.finditer(code_nostr):
                cname = cm.group(1)
                if cname in kws or cname in u.vars:
                    continue
                q, tid, mean, lab = self._resolve_foreign_call(fr, u, cname)
                col_c = cm.start(1)
                if tid >= 0:
                    self.add_edge(u, self.units[tid], "guess" if q == "g" else "call", ln)
                    fr.sem[(ln, col_c)] = ("c", tid, q, mean)
                elif mean:
                    fr.sem[(ln, col_c)] = ("e", mean)
                    u.ext_calls[lab] += 1
                u.cnt["calls"] += 1
                if lab not in seen_call:
                    seen_call.add(lab)
                    calls.append([lab + "()", tid, q, mean])
            for idm in re.finditer(r"\b([A-Za-z_]\w*)\b", code_nostr):
                nm = idm.group(1)
                if nm in u.vars:
                    col_v = idm.start(1)
                    if (ln, col_v) not in fr.sem:
                        fr.sem[(ln, col_v)] = ("v", nm)
                    if nm not in writes:
                        self.add_use(u, nm, ln)
                        if nm not in reads:
                            reads.append(nm)
            desc = f"`{', '.join(writes)}` 에 값을 대입합니다 (`{short(code, 56)}`)." if writes else (
                f"`{calls[0][0]}` 을(를) 호출합니다." if calls else f"`{short(code, 64)}` 를 실행합니다."
            )
            rec: Dict[str, Any] = {"k": kind if kind != "stmt" else ("callstmt" if calls else "stmt"),
                                  "a": ln, "z": ln, "t": kind, "x": desc, "u": u.id, "p": list(chain)}
            if reads:
                rec["r"] = reads[:8]
            if writes:
                rec["w"] = writes[:8]
            if calls:
                rec["c"] = [[c[0], c[1], c[2], short(c[3], 90)] for c in calls[:8]]
            fr.info[ln] = rec

    def compute_foreign_steps(self, u: Unit) -> None:
        if u.kind not in ("function", "module"):
            return
        fr = self.files[u.file]
        top_lines: List[int] = []
        for ln in range(u.line + (1 if u.kind == "function" else 0), u.end + 1):
            inf = fr.info.get(ln)
            if inf and inf.get("u") == u.id and not inf.get("p") and inf.get("k") not in ("cont", "blank", "comment", "else"):
                top_lines.append(ln)
        if not top_lines:
            return
        groups: List[List[int]] = []
        cur: List[int] = []
        for ln in top_lines:
            inf = fr.info[ln]
            k = inf.get("k", "")
            has_cmt = any(fr.line_is_comment(x) for x in range(max(u.line, ln - 2), ln))
            split = bool(cur) and (
                has_cmt or k in ("for", "while", "try", "if", "return")
                or fr.info[cur[-1]].get("k") in ("for", "while", "try", "if")
                or (ln - cur[0] + 1) > 10 or len(cur) >= 5
            )
            if split:
                groups.append(cur)
                cur = []
            cur.append(ln)
        if cur:
            groups.append(cur)
        while len(groups) > 6:
            i = min(range(len(groups) - 1), key=lambda k: groups[k + 1][-1] - groups[k][0])
            groups[i] = groups[i] + groups[i + 1]
            groups.pop(i + 1)
        param_names = {p["name"] for p in u.params if p["name"] != u.self_name}
        steps: List[dict] = []
        for idx, grp in enumerate(groups, start=1):
            l1 = grp[0]
            l2 = max(fr.info.get(x, {}).get("z", x) for x in grp)
            if idx < len(groups):
                l2 = min(l2, groups[idx][0] - 1)
            elif u.kind == "function":
                l2 = max(l2, min(u.end, grp[-1] + 4))
            reads, writes, calls, kinds = [], [], [], []
            for ln in range(l1, l2 + 1):
                inf = fr.info.get(ln)
                if not inf:
                    continue
                kinds.append(inf.get("k", ""))
                for r in inf.get("r") or []:
                    if r not in reads:
                        reads.append(r)
                for w in inf.get("w") or []:
                    if w not in writes:
                        writes.append(w)
                for c in inf.get("c") or []:
                    if c and c[0] not in [x[0] for x in calls]:
                        calls.append(c)
            from_earlier = [r for r in reads if r in param_names or any(d[0] < l1 for d in u.vars.get(r, {}).get("defs", []))]
            used_later = [w for w in writes if any(us > l2 for us in u.vars.get(w, {}).get("uses", []))]
            title = "반복 처리" if any(k in ("for", "while") for k in kinds) else (
                "예외 처리 블록" if "try" in kinds else (
                "조건 분기 처리" if "if" in kinds else (
                "결과 반환" if kinds and kinds[-1] == "return" else (
                f"{short(calls[0][0].rstrip('()'), 22)} 등 처리" if calls else (
                "초기 변수·상태 준비" if idx == 1 else "핵심 계산·처리"
            )))))
            desc = f"L{l1}–L{l2} 구간을 실행합니다."
            if calls:
                desc = f"{', '.join(f'`{c[0]}`' for c in calls[:3])} 호출과 계산을 수행합니다."
            elif writes:
                desc = f"`{', '.join(writes[:4])}` 변수 값을 계산·갱신합니다."
            why = (f"앞선 `{', '.join(from_earlier[:3])}` 를 받아 " if from_earlier else "") + (
                f"다음 단계의 `{', '.join(used_later[:3])}` 를 준비합니다." if used_later else "해당 단계의 역할을 수행합니다."
            )
            steps.append({"id": idx, "l1": l1, "l2": l2, "t": title, "d": desc, "w": why,
                          "r": from_earlier[:8], "wr": writes[:8], "ul": used_later[:8],
                          "c": [[c[0], c[1], c[2], short(c[3], 60)] for c in calls[:6]]})
        u.steps = steps


# ───────────────────────────── 분석기 본체 ─────────────────────────────
class Project(ResolverMixin, ForeignMixin):
    def __init__(self, root: Path, excludes: Optional[set] = None, log: Callable[[str], None] = print):
        self.root = Path(root)
        self.excludes = set(excludes or [])
        self.log = log
        self.files: List[FileRec] = []
        self.units: List[Unit] = []
        self.by_short: Dict[str, List[Unit]] = defaultdict(list)
        self.class_bases: Dict[int, List[Unit]] = {}
        self.class_attr_types: Dict[int, Dict[str, Unit]] = {}
        self.node_unit: Dict[int, Unit] = {}
        self.errors: List[str] = []
        self.order: Dict[str, Any] = {}
        self.ext_libs: Counter = Counter()

    # ────────── 로딩 ──────────
    def load(self) -> None:
        paths: List[Path] = []
        for dp, dns, fns in os.walk(self.root):
            dns[:] = sorted(d for d in dns if d not in IGNORE_DIRS and not d.startswith(".")
                            and d not in self.excludes)
            for fn in sorted(fns):
                ext = Path(fn).suffix.lower()
                if ext in LANG_EXTS:
                    paths.append(Path(dp) / fn)
        for p in paths:
            try:
                if p.stat().st_size > MAX_FILE_BYTES:
                    self.log(f"  [건너뜀] 파일이 너무 큼: {p.name}")
                    continue
                text = p.read_text(encoding="utf-8-sig", errors="replace")
            except OSError as e:
                self.log(f"  [건너뜀] 읽기 실패 {p.name}: {e}")
                continue
            rel = p.relative_to(self.root).as_posix()
            ext = p.suffix.lower()
            lang = LANG_EXTS.get(ext, "py")
            if ext == ".h" and re.search(r"\b(class|namespace|template|public:|private:|protected:|virtual)\b|::", text):
                lang = "cpp"
            parts = list(Path(rel).with_suffix("").parts)
            is_init = (lang == "py") and bool(parts) and parts[-1] == "__init__"
            if is_init:
                parts = parts[:-1]
            module = ".".join(parts) if parts else Path(rel).stem
            fr = FileRec(len(self.files), rel, module, text, is_init, lang=lang)
            if lang == "py":
                try:
                    fr.tree = ast.parse(fr.text, filename=rel)
                except (SyntaxError, ValueError, RecursionError) as e:
                    fr.err = f"{type(e).__name__}: {e}"
                    fr.tree = ast.Module(body=[], type_ignores=[])
                    self.log(f"  [구문 오류] {rel}: {fr.err} (정적 해설 없이 원문만 표시)")
                for n in ast.walk(fr.tree):
                    for c in ast.iter_child_nodes(n):
                        fr.parents[id(c)] = n
            elif lang in _TS_LANGS and _ts is not None:
                try:
                    parser = _ts.Parser(_TS_LANGS[lang])
                    fr.ts_tree = parser.parse(fr.text.encode("utf-8", "replace"))
                except Exception as e:
                    self.log(f"  [파싱 경고] {rel}: {e}")
            self.files.append(fr)
        if not self.files:
            raise ValueError("선택한 폴더에서 분석 가능한 소스 파일(.py/.js/.ts/.c/.cpp/.m)을 찾지 못했습니다.")

    # ────────── 단위(Unit) 생성 ──────────
    def new_unit(self, kind: str, name: str, fr: FileRec, node: ast.AST,
                 parent: Optional[Unit], cls: Optional[Unit]) -> Unit:
        u = Unit(len(self.units), kind, name, fr.idx, node, parent, cls)
        self.units.append(u)
        self.node_unit[id(node)] = u
        if kind == "module":
            u.disp = fr.module or fr.rel
            u.qual = f"{fr.module}.<module>"
            u.line, u.end = 1, max(1, len(fr.lines))
            u.doc = (ast.get_docstring(node) or "").strip()  # type: ignore[arg-type]
        else:
            chain, p = [], u
            while p is not None and p.kind != "module":
                chain.append(p.name)
                p = p.parent
            u.disp = ".".join(reversed(chain))
            u.qual = f"{fr.module}.{u.disp}"
            u.doc = (ast.get_docstring(node) or "").strip()  # type: ignore[arg-type]
            self.by_short[name].append(u)
        return u

    def collect_params(self, fr: FileRec, u: Unit) -> None:
        node = u.node
        a = node.args  # type: ignore[attr-defined]
        pos = a.posonlyargs + a.args
        defaults = [None] * (len(pos) - len(a.defaults)) + list(a.defaults)

        def mk(arg: ast.arg, kind: str, d: Optional[ast.AST]) -> dict:
            return {
                "name": arg.arg, "kind": kind, "line": arg.lineno, "col": arg.col_offset,
                "ann": short(fr.seg(arg.annotation), 40) if arg.annotation is not None else "",
                "ann_node": arg.annotation,
                "default": short(fr.seg(d), 30) if d is not None else None,
            }
        for arg, d in zip(pos, defaults):
            u.params.append(mk(arg, "pos", d))
        if a.vararg:
            u.params.append(mk(a.vararg, "var", None))
        for arg, d in zip(a.kwonlyargs, a.kw_defaults):
            u.params.append(mk(arg, "kw", d))
        if a.kwarg:
            u.params.append(mk(a.kwarg, "kwvar", None))

    def build_units(self, fr: FileRec) -> None:
        mod = self.new_unit("module", "<module>", fr, fr.tree, None, None)  # type: ignore[arg-type]
        fr.module_unit = mod
        self._fill_scope(fr, mod, fr.tree.body)  # type: ignore[union-attr]

    def _fill_scope(self, fr: FileRec, scope: Unit, body: List[ast.AST]) -> None:
        for st in iter_scope_stmts(body):
            scope.stmts.append(st)
            if isinstance(st, ast.Import):
                for a in st.names:
                    if a.asname:
                        scope.aliases[a.asname] = ("mod", a.name)
                    else:
                        top = a.name.split(".")[0]
                        scope.aliases[top] = ("mod", top)
                    fr.imports_all.add(a.name)
            elif isinstance(st, ast.ImportFrom):
                mod = self.resolve_relative(fr, st.level, st.module)
                for a in st.names:
                    if a.name == "*":
                        continue
                    scope.aliases[a.asname or a.name] = ("from", mod, a.name)
                    fr.imports_all.add((mod + "." + a.name) if mod else a.name)
                if mod:
                    fr.imports_all.add(mod)
            elif isinstance(st, SCOPE_TYPES):
                is_cls = isinstance(st, ast.ClassDef)
                kind = "class" if is_cls else "function"
                if is_cls:
                    cls = None
                else:
                    cls = scope if scope.kind == "class" else scope.cls
                u = self.new_unit(kind, st.name, fr, st, scope, cls)
                scope.local_defs[st.name] = u
                scope.children.append(u)
                u.decos = [short(fr.seg(d), 40) for d in st.decorator_list]
                if not is_cls:
                    self.collect_params(fr, u)
                    if st.returns is not None:  # type: ignore[union-attr]
                        u.ret_ann = short(fr.seg(st.returns), 40)  # type: ignore[union-attr]
                    if scope.kind == "class":
                        is_static = any(d.split(".")[-1] == "staticmethod" for d in u.decos)
                        if u.params and not is_static:
                            u.self_name = u.params[0]["name"]
                    else:
                        u.self_name = scope.self_name
                self._fill_scope(fr, u, st.body)

    def prepare_unit(self, u: Unit) -> None:
        names = set(p["name"] for p in u.params)
        for st in u.stmts:
            if isinstance(st, ast.ExceptHandler) and st.name:
                names.add(st.name)
            if isinstance(st, (ast.Global, ast.Nonlocal)):
                u.globals_declared.update(st.names)
            for e in header_exprs(st):
                for n in ast.walk(e):
                    if isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
                        names.add(n.id)
        u.local_names = names - u.globals_declared

    def compute_class_info(self) -> None:
        for u in self.units:
            if u.kind != "class" or self.files[u.file].lang != "py":
                continue
            bases: List[Unit] = []
            for b in u.node.bases:  # type: ignore[attr-defined]
                try:
                    r = self.resolve_expr(b, u.parent or u)
                    if r.kind == "class" and r.unit is not u:
                        bases.append(r.unit)  # type: ignore[arg-type]
                except Exception:
                    pass
            self.class_bases[u.id] = bases
        for u in self.units:
            if u.kind != "class" or self.files[u.file].lang != "py":
                continue
            types: Dict[str, Unit] = {}
            for st in u.stmts:
                if isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name):
                    c = self.ann_class(st.annotation, u)
                    if c is not None:
                        types[st.target.id] = c
            for m in u.children:
                if m.kind != "function" or not m.self_name:
                    continue
                vt = self.var_types(m)
                for st in m.stmts:
                    if isinstance(st, ast.Assign):
                        targets, value, ann = st.targets, st.value, None
                    elif isinstance(st, ast.AnnAssign):
                        targets, value, ann = [st.target], st.value, st.annotation
                    else:
                        continue
                    for t in targets:
                        if (isinstance(t, ast.Attribute) and isinstance(t.value, ast.Name)
                                and t.value.id == m.self_name):
                            c = self.ann_class(ann, m) if ann is not None else None
                            if c is None and value is not None:
                                c = self.class_of_value(value, m, vt)
                            if c is not None:
                                types.setdefault(t.attr, c)
            self.class_attr_types[u.id] = types

    # ────────── 변수 추적 ──────────
    def var(self, u: Unit, name: str, kind: str = "local") -> dict:
        v = u.vars.get(name)
        if v is None:
            v = u.vars[name] = {"name": name, "kind": kind, "type": "", "defs": [], "uses": []}
        return v

    def add_def(self, u: Unit, name: str, line: int, src: str, typ: str = "", kind: Optional[str] = None) -> None:
        v = self.var(u, name, kind or "local")
        if kind and v["kind"] in ("local", "comp") and kind in ("param", "import", "def", "attr"):
            v["kind"] = kind
        if len(v["defs"]) < 60:
            v["defs"].append([line, short(src, 70)])
        if typ and not v["type"]:
            v["type"] = typ

    def add_use(self, u: Unit, name: str, line: int) -> None:
        v = u.vars.get(name) or self.var(u, name, "local" if (name in u.local_names or name.startswith("self.")) else "global")
        if len(v["uses"]) < 200:
            v["uses"].append(line)

    def infer_type(self, v: Optional[ast.AST], u: Unit, vt: dict) -> str:
        if v is None:
            return ""
        try:
            if isinstance(v, ast.Constant):
                return "None" if v.value is None else type(v.value).__name__
            if isinstance(v, (ast.List, ast.ListComp)):
                return "list"
            if isinstance(v, (ast.Dict, ast.DictComp)):
                return "dict"
            if isinstance(v, (ast.Set, ast.SetComp)):
                return "set"
            if isinstance(v, ast.Tuple):
                return "tuple"
            if isinstance(v, ast.JoinedStr):
                return "str"
            if isinstance(v, ast.GeneratorExp):
                return "generator"
            if isinstance(v, ast.Compare) or (isinstance(v, ast.UnaryOp) and isinstance(v.op, ast.Not)):
                return "bool"
            if isinstance(v, ast.Lambda):
                return "function"
            if isinstance(v, ast.IfExp):
                return self.infer_type(v.body, u, vt) or self.infer_type(v.orelse, u, vt)
            if isinstance(v, ast.BinOp):
                l, r = self.infer_type(v.left, u, vt), self.infer_type(v.right, u, vt)
                if "str" in (l, r):
                    return "str"
                if l == r and l in ("int", "float", "list", "tuple"):
                    return l
                if {l, r} <= {"int", "float"} and l and r:
                    return "float"
                return ""
            if isinstance(v, ast.Name):
                if v.id in vt:
                    return vt[v.id].name
                if v.id in u.vars:
                    return u.vars[v.id]["type"]
                return ""
            if isinstance(v, ast.Call):
                res = self.resolve_expr(v.func, u, vt)
                if res.kind == "class":
                    return res.unit.name  # type: ignore[union-attr]
                if res.kind in ("unit", "guess"):
                    return res.unit.ret_ann  # type: ignore[union-attr]
                parts, _ = flatten_attr(v.func)
                last = parts[-1] if parts else ""
                if res.kind == "ext" and res.canon.startswith("numpy.") and last in NP_ARRAY_FUNCS:
                    return "ndarray"
                if len(parts) == 1 and last in TYPE_BY_NAME:
                    return TYPE_BY_NAME[last]
                if len(parts) > 1 and last in TYPE_BY_METHOD:
                    return TYPE_BY_METHOD[last]
                if res.kind == "ext" and res.canon.endswith("Path"):
                    return "Path"
        except Exception:
            pass
        return ""

    # ────────── 문장 분류/범위 ──────────
    def stmt_kind(self, fr: FileRec, st: ast.AST) -> str:
        if isinstance(st, ast.If):
            return "elif" if fr.lines[st.lineno - 1].lstrip().startswith("elif") else "if"
        m = [
            ((ast.Import, ast.ImportFrom), "import"), (DEF_TYPES, "def"), (ast.ClassDef, "class"),
            (ast.Assign, "assign"), (ast.AugAssign, "augassign"), (ast.AnnAssign, "annassign"),
            (ast.Return, "return"), (ast.Raise, "raise"), (ast.Assert, "assert"),
            ((ast.For, ast.AsyncFor), "for"), (ast.While, "while"),
            ((ast.With, ast.AsyncWith), "with"), (TRY_TYPES, "try"), (ast.ExceptHandler, "except"),
            (ast.Delete, "delete"), ((ast.Global, ast.Nonlocal), "global"), (ast.Pass, "pass"),
            (ast.Break, "break"), (ast.Continue, "continue"),
        ]
        for t, k in m:
            if isinstance(st, t):
                return k
        if hasattr(ast, "Match") and isinstance(st, ast.Match):
            return "match"
        if isinstance(st, ast.Expr):
            v = st.value
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                par = self_parent_body0(self, fr, st)
                return "docstring" if par else "expr"
            return "callstmt" if isinstance(v, ast.Call) else "expr"
        return "stmt"

    def stmt_range(self, fr: FileRec, st: ast.AST) -> Tuple[int, int]:
        a = st.lineno  # type: ignore[attr-defined]
        decos = getattr(st, "decorator_list", None)
        if decos:
            a = min([a] + [d.lineno for d in decos])
        body = getattr(st, "body", None)
        compound = isinstance(body, list) and body and isinstance(st, (
            ast.If, ast.For, ast.AsyncFor, ast.While, ast.With, ast.AsyncWith, ast.ExceptHandler,
            ast.ClassDef, *DEF_TYPES, *TRY_TYPES))
        if hasattr(ast, "Match") and isinstance(st, ast.Match):
            return a, st.lineno
        if not compound:
            return a, getattr(st, "end_lineno", st.lineno) or st.lineno
        first_child = body[0].lineno
        z = first_child - 1 if first_child > st.lineno else st.lineno
        floor = st.lineno
        for e in header_exprs(st):
            floor = max(floor, getattr(e, "end_lineno", floor) or floor)
        while z > floor and (fr.line_is_blank(z) or fr.line_is_comment(z)):
            z -= 1
        return a, max(z, st.lineno)

    def chain_of(self, fr: FileRec, st: ast.AST, scope_node: ast.AST) -> List[list]:
        out: List[list] = []
        child, p = st, fr.parents.get(id(st))
        while p is not None and p is not scope_node:
            if isinstance(p, CHAIN_TYPES):
                tag = ""
                if isinstance(p, (ast.If, ast.For, ast.AsyncFor, ast.While)) and any(child is x for x in p.orelse):
                    tag = "e"
                elif isinstance(p, TRY_TYPES):
                    if any(child is x for x in p.orelse):
                        tag = "e"
                    elif any(child is x for x in p.finalbody):
                        tag = "f"
                    elif any(child is x for x in p.body):
                        tag = "t"
                is_elif_link = (isinstance(p, ast.If) and tag == "e" and isinstance(child, ast.If)
                                and len(p.orelse) == 1
                                and fr.lines[child.lineno - 1].lstrip().startswith("elif"))
                if not is_elif_link:
                    out.append([p.lineno, tag])
            child, p = p, fr.parents.get(id(p))
        out.reverse()
        return out

    def target_ids(self, st: ast.AST) -> set:
        tgts: List[ast.AST] = []
        if isinstance(st, ast.Assign):
            tgts = list(st.targets)
        elif isinstance(st, (ast.AnnAssign, ast.AugAssign)):
            tgts = [st.target]
        elif isinstance(st, (ast.For, ast.AsyncFor)):
            tgts = [st.target]
        elif isinstance(st, (ast.With, ast.AsyncWith)):
            tgts = [it.optional_vars for it in st.items if it.optional_vars is not None]
        return {id(x) for t in tgts for x in ast.walk(t)}

    def def_src(self, fr: FileRec, st: ast.AST, n: ast.AST, tids: set) -> str:
        if id(n) not in tids:
            return "(식 안에서 만들어진 변수)"
        par = fr.parents.get(id(n))
        unpack = isinstance(par, (ast.Tuple, ast.List, ast.Starred))
        if isinstance(st, ast.Assign):
            return ("언패킹: " if unpack else "") + fr.seg(st.value)
        if isinstance(st, ast.AnnAssign):
            return fr.seg(st.value) if st.value is not None else "(타입만 선언)"
        if isinstance(st, ast.AugAssign):
            nm = n.id if isinstance(n, ast.Name) else getattr(n, "attr", "?")
            return f"{nm} {OP_SYMS.get(type(st.op), '?')}= {fr.seg(st.value)}"
        if isinstance(st, (ast.For, ast.AsyncFor)):
            return fr.seg(st.iter) + " 의 원소"
        if isinstance(st, (ast.With, ast.AsyncWith)):
            for it in st.items:
                if it.optional_vars is not None and any(x is n for x in ast.walk(it.optional_vars)):
                    return fr.seg(it.context_expr)
        return "(대입)"

    # ────────── 호출 처리 ──────────
    def add_edge(self, u: Unit, tgt: Unit, kind: str, line: int) -> None:
        if tgt is u and kind == "ref":
            return
        e = u.callees.get(tgt.id)
        if e is None:
            e = u.callees[tgt.id] = {"k": kind, "lines": []}
        rank = {"call": 3, "ref": 2, "guess": 1}
        if rank[kind] > rank[e["k"]]:
            e["k"] = kind
        if line not in e["lines"] and len(e["lines"]) < 30:
            e["lines"].append(line)

    def unit_tip(self, t: Unit) -> str:
        return f"프로젝트 {'클래스' if t.kind == 'class' else '함수'} `{t.disp}` ({self.files[t.file].rel}:{t.line})"

    def make_call(self, fr: FileRec, u: Unit, n: ast.Call, vt: dict, skip_sem: bool) -> dict:
        func = n.func
        res = self.resolve_expr(func, u, vt)
        parts, cbase = flatten_attr(func)
        label = ("(…)." + ".".join(parts)) if cbase is not None else short(fr.seg(func), 40)
        last = parts[-1] if parts else ""
        q, tid, meaning, canon = "?", -1, "", ""
        if res.kind == "unit":
            t = res.unit
            q, tid, meaning = "u", t.id, self.unit_tip(t)  # type: ignore[union-attr]
            self.add_edge(u, t, "call", n.lineno)  # type: ignore[arg-type]
        elif res.kind == "guess":
            t = res.unit
            q, tid, meaning = "g", t.id, "(추정) " + self.unit_tip(t)  # type: ignore[union-attr]
            self.add_edge(u, t, "guess", n.lineno)  # type: ignore[arg-type]
        elif res.kind == "class":
            c = res.unit
            init = self.find_method(c, "__init__")  # type: ignore[arg-type]
            if init is not None:
                q, tid = "k", init.id
                meaning = f"클래스 `{c.name}` 인스턴스 생성 → `__init__` 실행 ({self.files[init.file].rel}:{init.line})"  # type: ignore[union-attr]
                self.add_edge(u, init, "call", n.lineno)
            else:
                q, meaning = "kn", f"클래스 `{c.name}` 인스턴스 생성"  # type: ignore[union-attr]
        elif res.kind == "ext":
            canon = res.canon
            q = "e"
            meaning = kb_lookup(canon, last)
            u.ext_calls[canon] += 1
            ef = effect_of(canon, last)
            if ef:
                u.effects.add(ef)
        else:
            meaning = ("(일반적으로) " + KB_METHODS[last]) if (last in KB_METHODS and (len(parts) > 1 or cbase is not None)) else ""
            ef = effect_of(".".join(parts), last) if (len(parts) > 1 or cbase is not None) else None
            if ef:
                u.effects.add(ef)
        if not skip_sem:
            if isinstance(func, ast.Name):
                key = (func.lineno, fr.cc(func.lineno, func.col_offset))
            elif isinstance(func, ast.Attribute) and getattr(func, "end_lineno", None):
                key = (func.end_lineno, fr.cc(func.end_lineno, func.end_col_offset) - len(func.attr))
            else:
                key = None
            if key is not None:
                if q in ("u", "k", "g"):
                    fr.sem[key] = ("c", tid, q, meaning)
                elif meaning:
                    fr.sem[key] = ("e", meaning)
        return {"node": n, "q": q, "id": tid, "label": label, "meaning": meaning, "canon": canon}

    # ────────── 스코프/문장 분석 ──────────
    def analyze_scope(self, u: Unit) -> None:
        fr = self.files[u.file]
        vt = self.var_types(u)
        for p in u.params:
            self.add_def(u, p["name"], p["line"], "(매개변수)" + (f" 기본값 {p['default']}" if p["default"] else ""),
                         p["ann"], kind="param")
            if p["name"] != u.self_name:
                fr.sem.setdefault((p["line"], fr.cc(p["line"], p["col"])), ("v", p["name"]))
        for st in u.stmts:
            try:
                self.analyze_stmt(fr, u, st, vt)
            except Exception as e:  # 한 문장의 실패가 전체를 막지 않도록
                self.errors.append(f"{fr.rel}:{getattr(st, 'lineno', '?')}: {type(e).__name__}: {e}")
                a, z = self.stmt_range(fr, st)
                for ln in range(a, z + 1):
                    fr.info.setdefault(ln, {"k": "stmt", "a": a, "z": z, "t": "문장", "x": short(fr.lines[ln - 1].strip(), 80), "u": u.id})

    def var_key(self, node: ast.AST, u: Unit) -> Optional[str]:
        if isinstance(node, ast.Name):
            return None if node.id == u.self_name else node.id
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and u.self_name \
                and node.value.id == u.self_name:
            return f"self.{node.attr}"
        return None

    def note_external(self, u: Unit, name: str, line: int) -> None:
        if name in u.externals or name in BUILTINS:
            return
        r = self.resolve_name(name, u)
        if r is None:
            return
        tag, val = r
        if tag == "unit":
            u.externals[name] = {"kind": "cls" if val.kind == "class" else "fn", "id": val.id, "line": line}
        elif tag == "module":
            u.externals[name] = {"kind": "mod", "id": self.files[val].module_unit.id, "line": line}
        elif tag == "ext":
            u.externals[name] = {"kind": "lib", "canon": val, "line": line}
            self.ext_libs[val.split(".")[0]] += 1

    def analyze_stmt(self, fr: FileRec, u: Unit, st: ast.AST, vt: dict) -> None:
        kind = self.stmt_kind(fr, st)
        a, z = self.stmt_range(fr, st)
        nodes: List[ast.AST] = []
        for e in header_exprs(st):
            nodes.extend(ast.walk(e))
        nodes.sort(key=lambda n: (getattr(n, "lineno", 0), getattr(n, "col_offset", 0)))
        callee_ids = {id(n.func) for n in nodes if isinstance(n, ast.Call)}
        attr_inner = {id(n.value) for n in nodes if isinstance(n, ast.Attribute)}
        skip_sem: set = set()
        if sys.version_info < (3, 12):
            for n in nodes:
                if isinstance(n, ast.JoinedStr):
                    skip_sem.update(id(d) for d in ast.walk(n))
        tids = self.target_ids(st)
        mod_names = self.files[u.file].module_unit.local_names  # type: ignore[union-attr]
        reads: List[str] = []
        writes: List[str] = []
        muts: List[str] = []
        cinfos: List[dict] = []
        cmap: Dict[int, dict] = {}
        chips_ref: List[list] = []
        seen_before = set(u.vars.keys())

        def uniq(lst: List[str], x: str) -> None:
            if x not in lst:
                lst.append(x)

        for n in nodes:
            lineno = getattr(n, "lineno", a)
            if isinstance(n, ast.Call):
                ci = self.make_call(fr, u, n, vt, id(n) in skip_sem or id(n.func) in skip_sem)
                cinfos.append(ci)
                cmap[id(n)] = ci
                f = n.func
                if isinstance(f, ast.Attribute) and f.attr in MUTATORS:
                    k = self.var_key(f.value, u)
                    if k:
                        uniq(muts, k)
                u.cnt["calls"] += 1
            elif isinstance(n, ast.Name):
                name = n.id
                if name == u.self_name:
                    continue
                store = isinstance(n.ctx, (ast.Store, ast.Del))
                is_var = name in u.local_names or name in mod_names
                if store:
                    src = self.def_src(fr, st, n, tids)
                    typ = ""
                    if id(n) in tids:
                        par = fr.parents.get(id(n))
                        if isinstance(st, ast.Assign) and par is st:
                            typ = self.infer_type(st.value, u, vt)
                        elif isinstance(st, ast.AnnAssign):
                            typ = short(fr.seg(st.annotation), 30) or self.infer_type(st.value, u, vt)
                        elif isinstance(st, ast.AugAssign):
                            typ = u.vars.get(name, {}).get("type", "")
                    self.add_def(u, name, lineno, src, typ, kind="local" if id(n) in tids else "comp")
                    uniq(writes, name)
                    if isinstance(st, ast.AugAssign) and n is st.target:
                        uniq(reads, name)
                        self.add_use(u, name, lineno)
                    fr.sem.setdefault((lineno, fr.cc(lineno, n.col_offset)), ("v", name)) if id(n) not in skip_sem else None
                else:
                    if is_var:
                        if id(n) not in callee_ids or name in u.local_names:
                            uniq(reads, name)
                            self.add_use(u, name, lineno)
                        if id(n) not in skip_sem:
                            fr.sem.setdefault((lineno, fr.cc(lineno, n.col_offset)), ("v", name))
                    else:
                        self.note_external(u, name, lineno)
                    if id(n) not in callee_ids and id(n) not in attr_inner and not is_var:
                        res = self.resolve_expr(n, u, vt)
                        if res.kind == "unit" and res.unit is not u:
                            self.add_edge(u, res.unit, "ref", lineno)  # type: ignore[arg-type]
                            chips_ref.append([name, res.unit.id, "r", self.unit_tip(res.unit)])  # type: ignore[union-attr]
                            if id(n) not in skip_sem:
                                fr.sem[(lineno, fr.cc(lineno, n.col_offset))] = ("r", res.unit.id, self.unit_tip(res.unit))  # type: ignore[union-attr]
            elif isinstance(n, ast.Attribute):
                end_ok = getattr(n, "end_lineno", None) is not None
                key = self.var_key(n, u)
                store = isinstance(n.ctx, (ast.Store, ast.Del))
                is_callee = id(n) in callee_ids
                is_inner = id(n) in attr_inner
                if key and end_ok:
                    is_method = (not store) and u.cls is not None and self.find_method(u.cls, n.attr) is not None
                    pos = (n.end_lineno, fr.cc(n.end_lineno, n.end_col_offset) - len(n.attr))
                    if store or not is_method:
                        if store:
                            src = self.def_src(fr, st, n, tids)
                            typ = self.infer_type(st.value, u, vt) if isinstance(st, ast.Assign) and id(n) in tids else ""
                            if isinstance(st, ast.AnnAssign):
                                typ = short(fr.seg(st.annotation), 30)
                            self.add_def(u, key, n.end_lineno, src, typ, kind="attr")
                            uniq(writes, key)
                            if isinstance(st, ast.AugAssign) and n is st.target:
                                uniq(reads, key)
                                self.add_use(u, key, n.end_lineno)
                            if id(n) not in skip_sem:
                                fr.sem.setdefault(pos, ("v", key))
                        elif not is_callee:
                            uniq(reads, key)
                            self.add_use(u, key, n.end_lineno)
                            if id(n) not in skip_sem:
                                fr.sem.setdefault(pos, ("v", key))
                    elif not is_callee and not is_inner:
                        res = self.resolve_expr(n, u, vt)
                        if res.kind == "unit" and res.unit is not u:
                            self.add_edge(u, res.unit, "ref", n.end_lineno)  # type: ignore[arg-type]
                            chips_ref.append([key, res.unit.id, "r", self.unit_tip(res.unit)])  # type: ignore[union-attr]
                            if id(n) not in skip_sem:
                                fr.sem[pos] = ("r", res.unit.id, self.unit_tip(res.unit))  # type: ignore[union-attr]
                elif store:
                    k2 = self.var_key(n.value, u)
                    if k2:
                        uniq(muts, k2)
                elif end_ok and not is_callee and not is_inner:
                    res = self.resolve_expr(n, u, vt)
                    if res.kind == "unit" and res.unit is not u:
                        self.add_edge(u, res.unit, "ref", n.end_lineno)  # type: ignore[arg-type]
                        chips_ref.append([short(fr.seg(n), 30), res.unit.id, "r", self.unit_tip(res.unit)])  # type: ignore[union-attr]
                        if id(n) not in skip_sem:
                            pos = (n.end_lineno, fr.cc(n.end_lineno, n.end_col_offset) - len(n.attr))
                            fr.sem[pos] = ("r", res.unit.id, self.unit_tip(res.unit))  # type: ignore[union-attr]
            elif isinstance(n, ast.Subscript) and isinstance(n.ctx, (ast.Store, ast.Del)):
                k = self.var_key(n.value, u)
                if k:
                    uniq(muts, k)
            elif isinstance(n, ast.BoolOp):
                u.cnt["boolop"] += len(n.values) - 1
            elif isinstance(n, ast.IfExp):
                u.cnt["ifexp"] += 1
            elif isinstance(n, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
                u.cnt["comp"] += 1
                u.cnt["compif"] += sum(len(g.ifs) for g in n.generators)
            elif isinstance(n, (ast.Yield, ast.YieldFrom)):
                u.cnt["yield"] += 1
            elif isinstance(n, ast.Lambda):
                u.cnt["lambda"] += 1

        # 문장 고유 정의(이름 바인딩)
        line0 = st.lineno  # type: ignore[attr-defined]
        if isinstance(st, ast.Import):
            for al in st.names:
                nm = al.asname or al.name.split(".")[0]
                self.add_def(u, nm, line0, "import " + al.name, "module", kind="import")
                writes.append(nm)
        elif isinstance(st, ast.ImportFrom):
            mod = self.resolve_relative(fr, st.level, st.module)
            for al in st.names:
                nm = al.asname or al.name
                self.add_def(u, nm, line0, f"from {mod} import {al.name}", "", kind="import")
                writes.append(nm)
        elif isinstance(st, SCOPE_TYPES):
            self.add_def(u, st.name, line0, "def" if not isinstance(st, ast.ClassDef) else "class", "function" if not isinstance(st, ast.ClassDef) else "class", kind="def")
            writes.append(st.name)
        elif isinstance(st, ast.ExceptHandler) and st.name:
            self.add_def(u, st.name, line0, "예외 객체", short(fr.seg(st.type), 30) if st.type is not None else "Exception")
            writes.append(st.name)

        # 카운터/반환값
        cnt_key = {"if": "if", "elif": "if", "for": "for", "while": "while", "except": "except",
                   "with": "with", "try": "try", "return": "return", "raise": "raise", "assert": "assert"}.get(kind)
        if cnt_key:
            u.cnt[cnt_key] += 1
        if isinstance(st, ast.Return):
            r = short(fr.seg(st.value), 40) if st.value is not None else "None"
            if r not in u.rets:
                u.rets.append(r)

        scope_node = u.node
        chain = self.chain_of(fr, st, scope_node)
        u.depth = max(u.depth, len(chain))

        title, text, hint = self.explain(fr, u, st, kind, {
            "cmap": cmap, "vt": vt, "seen": seen_before, "cinfos": cinfos, "reads": reads,
            "writes": writes, "muts": muts,
        })
        rec: Dict[str, Any] = {"k": kind, "a": a, "z": z, "t": title, "x": text, "u": u.id, "p": chain}
        if hint:
            rec["h"] = hint
        rds = [r for r in reads if r != "self"][:10]
        if rds:
            rec["r"] = rds
        if writes:
            rec["w"] = writes[:10]
        if muts:
            rec["m"] = muts[:6]
        chips = [[c["label"] + "()", c["id"], c["q"], short(c["meaning"], 90)] for c in cinfos[:10]]
        chips += chips_ref[:4]
        if chips:
            rec["c"] = chips
        if isinstance(st, SCOPE_TYPES):
            du = self.node_unit.get(id(st))
            if du is not None:
                rec["d"] = du.id
        # 앞 주석 / 줄 끝 주석
        cm: List[str] = []
        ln = a - 1
        while ln >= 1 and fr.line_is_comment(ln):
            cm.insert(0, fr.lines[ln - 1].strip().lstrip("#").strip())
            ln -= 1
        tail = fr.comments.get(a)
        if tail and not tail[1]:
            cm.append(tail[0])
        if cm:
            rec["cm"] = short(" / ".join(c for c in cm if c), 220)

        for ln2 in range(a, z + 1):
            if ln2 == a:
                if a in fr.info and fr.info[a].get("k") not in ("cont", None):
                    fr.info[a].setdefault("mx", []).append(rec)
                else:
                    fr.info[a] = rec
            else:
                fr.info.setdefault(ln2, {"k": "cont", "a": a, "z": z, "u": u.id})

        # 합성 라인: else / finally
        if isinstance(st, (ast.If, ast.For, ast.AsyncFor, ast.While, *TRY_TYPES)) and st.orelse:  # type: ignore[attr-defined]
            first = st.orelse[0]  # type: ignore[attr-defined]
            is_elif = (isinstance(st, ast.If) and len(st.orelse) == 1 and isinstance(first, ast.If)
                       and fr.lines[first.lineno - 1].lstrip().startswith("elif"))
            if not is_elif:
                el = find_kw_line(fr, first.lineno, "else")
                if el:
                    self.add_synth(fr, u, st, el, "else", chain)
        if isinstance(st, TRY_TYPES) and st.finalbody:  # type: ignore[attr-defined]
            fl = find_kw_line(fr, st.finalbody[0].lineno, "finally")  # type: ignore[attr-defined]
            if fl:
                self.add_synth(fr, u, st, fl, "finally", chain)

        # 개요(outline)
        interesting = kind in ("if", "elif", "for", "while", "try", "except", "with", "return", "raise",
                               "break", "continue") or any(c["q"] in ("u", "k") for c in cinfos) or chips_ref
        if interesting and u.kind != "class" and len(u.outline) < 120:
            names = []
            for c in cinfos:
                if c["q"] in ("u", "k") and c["label"] not in names:
                    names.append(c["label"])
            it = {"l": a, "d": len(chain), "k": kind, "t": short(fr.lines[st.lineno - 1].strip(), 72)}  # type: ignore[attr-defined]
            if names:
                it["c"] = names[:3]
            u.outline.append(it)

    def add_synth(self, fr: FileRec, u: Unit, st: ast.AST, line: int, which: str, chain: List[list]) -> None:
        head = short(fr.lines[st.lineno - 1].strip(), 60)  # type: ignore[attr-defined]
        if which == "else":
            if isinstance(st, ast.If):
                text = f"위의 조건(`{short(fr.seg(st.test), 40)}`)이 모두 거짓일 때 실행되는 블록입니다."
            elif isinstance(st, (ast.For, ast.AsyncFor, ast.While)):
                text = "반복이 `break` 없이 정상적으로 끝났을 때 한 번 실행되는 블록입니다 (for/while-else)."
            else:
                text = "try 블록에서 예외가 발생하지 않았을 때만 실행되는 블록입니다."
            title = "else"
        else:
            text = "예외 발생 여부와 관계없이 항상 마지막에 실행되는 정리(finally) 블록입니다."
            title = "finally"
        rec = {"k": which, "a": line, "z": line, "t": title, "x": text, "u": u.id, "p": chain,
               "h": f"짝이 되는 문장: {head}"}
        fr.info[line] = fr.info.get(line) if (line in fr.info and fr.info[line].get("k") not in ("cont", None)) else rec
        if fr.info[line] is not rec and fr.info[line].get("k") != which:
            fr.info[line].setdefault("mx", []).append(rec)
        if u.kind != "class" and len(u.outline) < 120:
            u.outline.append({"l": line, "d": len(chain), "k": which, "t": which + ":"})

    # ────────── 줄별 한국어 해설 생성 (100% 결정적) ──────────
    def explain(self, fr: FileRec, u: Unit, st: ast.AST, kind: str, ctx: dict) -> Tuple[str, str, str]:
        try:
            return self._explain(fr, u, st, kind, ctx)
        except Exception as e:  # pragma: no cover
            self.errors.append(f"explain {fr.rel}:{getattr(st, 'lineno', '?')}: {e}")
            return ("문장", short(fr.lines[st.lineno - 1].strip(), 80), "")  # type: ignore[attr-defined]

    def cond_hint(self, fr: FileRec, test: ast.AST) -> str:
        F = lambda n, k=40: "`" + short(fr.seg(n), k).replace("`", "'") + "`"
        if isinstance(test, ast.UnaryOp) and isinstance(test.op, ast.Not):
            return f"`not X` 형태: {F(test.operand, 30)} 이(가) False·None·0·빈 값일 때 참이 됩니다."
        if isinstance(test, ast.Compare):
            ops = test.ops
            if len(ops) == 1:
                op, cmp0 = ops[0], test.comparators[0]
                none = isinstance(cmp0, ast.Constant) and cmp0.value is None
                if isinstance(op, ast.Is) and none:
                    return f"{F(test.left, 30)} 이(가) None 인지 검사합니다."
                if isinstance(op, ast.IsNot) and none:
                    return f"{F(test.left, 30)} 이(가) None 이 아닌지 검사합니다."
                if isinstance(op, ast.In):
                    return f"{F(test.left, 30)} 이(가) {F(cmp0, 30)} 안에 들어 있는지 검사합니다."
                if isinstance(op, ast.NotIn):
                    return f"{F(test.left, 30)} 이(가) {F(cmp0, 30)} 안에 없는지 검사합니다."
                if isinstance(op, (ast.Eq, ast.NotEq)):
                    return "두 값이 같은지(또는 다른지) 비교합니다."
                if isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                    return "두 값의 크기를 비교합니다."
            return "여러 비교를 연결한 조건입니다."
        if isinstance(test, ast.BoolOp):
            return "모든 조건이 참이어야 합니다(and)." if isinstance(test.op, ast.And) else "하나라도 참이면 됩니다(or)."
        if isinstance(test, ast.Call):
            parts, _ = flatten_attr(test.func)
            if parts and parts[-1] == "isinstance":
                return "객체의 타입을 검사합니다."
            return "함수의 반환값이 '참'으로 평가되는지 봅니다."
        if isinstance(test, (ast.Name, ast.Attribute)):
            return "값이 '참'으로 평가되는지(None·0·빈 컨테이너가 아닌지) 봅니다."
        return ""

    def _explain(self, fr: FileRec, u: Unit, st: ast.AST, kind: str, ctx: dict) -> Tuple[str, str, str]:
        cmap = ctx["cmap"]
        seen = ctx["seen"]
        muts = ctx["muts"]

        def F(n: ast.AST, k: int = 50) -> str:
            return "`" + short(fr.seg(n), k).replace("`", "'") + "`"

        def callmean(c: ast.Call) -> str:
            ci = cmap.get(id(c))
            nm = "`" + (ci["label"] if ci else short(fr.seg(c.func), 30)).replace("`", "'") + "()`"
            if not ci:
                return f"{nm} 의 반환값"
            q = ci["q"]
            if q == "u":
                return f"프로젝트 함수 {nm} 의 반환값"
            if q == "g":
                return f"(추정) 프로젝트 함수 {nm} 의 반환값"
            if q in ("k", "kn"):
                return f"새 객체(인스턴스) — {nm} 로 생성"
            if ci["meaning"]:
                return f"{nm} 의 결과 ({ci['meaning']})"
            return f"{nm} 의 반환값"

        def val(v: ast.AST) -> str:
            if isinstance(v, ast.Constant):
                x = v.value
                if x is None:
                    return "`None`"
                if isinstance(x, bool):
                    return f"불리언 `{x}`"
                if isinstance(x, (int, float, complex)):
                    return f"숫자 `{short(repr(x), 20)}`"
                if isinstance(x, str):
                    return f"문자열 `{short(repr(x), 30)}`".replace("``", "`")
                if isinstance(x, bytes):
                    return "바이트열"
                return F(v)
            if isinstance(v, ast.List):
                return "빈 리스트" if not v.elts else f"리스트(원소 {len(v.elts)}개)"
            if isinstance(v, ast.Tuple):
                return "빈 튜플" if not v.elts else f"튜플(원소 {len(v.elts)}개)"
            if isinstance(v, ast.Set):
                return f"집합(원소 {len(v.elts)}개)"
            if isinstance(v, ast.Dict):
                return "빈 딕셔너리" if not v.keys else f"딕셔너리(키 {len(v.keys)}개)"
            if isinstance(v, (ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)):
                nm = {ast.ListComp: "리스트", ast.SetComp: "집합", ast.GeneratorExp: "제너레이터", ast.DictComp: "딕셔너리"}[type(v)]
                g = v.generators[0]
                flt = " (조건 필터 포함)" if g.ifs else ""
                return f"{nm} 컴프리헨션 — {F(g.iter, 30)} 의 각 원소마다 계산해 만든 {nm}{flt}"
            if isinstance(v, ast.JoinedStr):
                return "f-문자열(값을 끼워 넣어 만든 문자열)"
            if isinstance(v, ast.Call):
                return callmean(v)
            if isinstance(v, ast.BinOp):
                return f"{F(v, 44)} 계산 결과"
            if isinstance(v, ast.UnaryOp):
                return f"{F(v, 40)} 의 결과"
            if isinstance(v, (ast.BoolOp, ast.Compare)):
                return f"조건식 {F(v, 44)} 의 결과"
            if isinstance(v, ast.IfExp):
                return f"조건 {F(v.test, 24)} 에 따라 고른 값({F(v.body, 18)} 또는 {F(v.orelse, 18)})"
            if isinstance(v, ast.Lambda):
                return "람다(이름 없는 함수)"
            if isinstance(v, ast.Subscript):
                return f"{F(v, 40)} (인덱싱/슬라이싱으로 꺼낸 값)"
            if isinstance(v, ast.Await):
                return "await 로 기다린 결과"
            return f"{F(v, 44)} 의 값"

        hint = ""
        if kind == "import":
            if isinstance(st, ast.Import):
                items = []
                for al in st.names:
                    f = self.find_module(al.name)
                    tag = f" (프로젝트 파일 {self.files[f].rel})" if f is not None else ""
                    items.append(f"`{al.name}`" + (f" → `{al.asname}`" if al.asname else "") + tag)
                return "모듈 불러오기", "모듈 " + ", ".join(items) + " 를 불러와 사용할 수 있게 합니다.", ""
            mod = self.resolve_relative(fr, st.level, st.module)  # type: ignore[attr-defined]
            f = self.find_module(mod)
            where = f" (프로젝트 파일 {self.files[f].rel})" if f is not None else " (외부 라이브러리/표준 라이브러리)"
            names = ", ".join(f"`{a.name}`" + (f" → `{a.asname}`" if a.asname else "") for a in st.names)  # type: ignore[attr-defined]
            return "모듈 불러오기", f"`{mod or '.'}`{where} 에서 {names} 를 가져옵니다.", ""

        if kind == "def":
            d = self.node_unit.get(id(st))
            sig = ", ".join(p["name"] for p in d.params) if d else ""
            pre = "비동기 " if isinstance(st, ast.AsyncFunctionDef) else ""
            what = "메서드" if (d and d.parent is not None and d.parent.kind == "class") else "함수"
            text = f"{pre}{what} `{st.name}({sig})` 를 정의합니다. 이 줄은 '정의'만 하며, 본문은 호출될 때 실행됩니다."  # type: ignore[attr-defined]
            if d and d.decos:
                parts = []
                for dc in d.decos:
                    base = dc.split("(")[0].split(".")[-1]
                    parts.append(f"`@{dc}`" + (f" ({DECORATOR_KB[base]})" if base in DECORATOR_KB else ""))
                text += " 데코레이터: " + ", ".join(parts) + "."
            if d and d.ret_ann:
                text += f" 반환 타입 표기: `{d.ret_ann}`."
            return f"{what} 정의", text, ""

        if kind == "class":
            d = self.node_unit.get(id(st))
            bases = ", ".join(f"`{short(fr.seg(b), 24)}`" for b in st.bases)  # type: ignore[attr-defined]
            nmeth = len([c for c in d.children if c.kind == "function"]) if d else 0
            text = f"클래스 `{st.name}` 를 정의합니다" + (f" (상속: {bases})" if bases else "") + f". 메서드 {nmeth}개를 가집니다."  # type: ignore[attr-defined]
            if d and d.decos:
                text += " 데코레이터: " + ", ".join(f"`@{x}`" for x in d.decos) + "."
            return "클래스 정의", text, ""

        if kind == "assign":
            tg = st.targets  # type: ignore[attr-defined]
            t0 = tg[0]
            desc = val(st.value)  # type: ignore[attr-defined]
            if isinstance(t0, (ast.Tuple, ast.List)):
                text = f"{F(t0, 40)} 에 {desc} 을(를) 풀어서(언패킹) 나눠 담습니다."
            elif isinstance(t0, ast.Subscript):
                text = f"{F(t0, 40)} 항목에 {desc} 을(를) 저장합니다 (컨테이너 내용이 바뀝니다)."
            elif isinstance(t0, ast.Attribute):
                text = f"객체 속성 {F(t0, 40)} 에 {desc} 을(를) 저장합니다 (객체 상태가 바뀝니다)."
            else:
                nm = getattr(t0, "id", "?")
                text = f"변수 `{nm}` 에 {desc} 을(를) 저장합니다 ({'기존 변수 값 갱신' if nm in seen else '새 변수'})."
            if len(tg) > 1:
                text += f" 같은 값을 {len(tg)}개 이름에 동시에 저장합니다."
            nm0 = t0.id if isinstance(t0, ast.Name) else (self.var_key(t0, u) if isinstance(t0, ast.Attribute) else None)
            ty = u.vars.get(nm0, {}).get("type", "") if nm0 else ""
            if ty:
                hint = f"추정 타입: {ty}"
            return "대입", text, hint

        if kind == "augassign":
            op = OP_NAMES.get(type(st.op), "연산해서")  # type: ignore[attr-defined]
            return "누적 대입", f"{F(st.target, 30)} 의 기존 값에 {val(st.value)} 을(를) {op} 다시 저장합니다.", ""  # type: ignore[attr-defined]

        if kind == "annassign":
            text = f"{F(st.target, 30)} 를 타입 `{short(fr.seg(st.annotation), 30)}` 로 선언합니다"  # type: ignore[attr-defined]
            text += (f" 그리고 {val(st.value)} 을(를) 저장합니다." if st.value is not None else " (값은 아직 없음).")  # type: ignore[attr-defined]
            return "타입 표기 대입", text, ""

        if kind == "callstmt":
            c = st.value  # type: ignore[attr-defined]
            ci = cmap.get(id(c))
            what = ci["meaning"] if ci and ci["meaning"] else ""
            lab = "`" + (ci["label"] if ci else short(fr.seg(c.func), 30)).replace("`", "'") + "()`"
            text = f"{lab} 를 호출합니다" + (f" — {what}" if what else "") + ". 반환값을 쓰지 않으므로 상태 변경·출력·저장 같은 '부작용'이 목적입니다."
            if muts:
                text += " 이 호출로 " + ", ".join(f"`{m}`" for m in muts[:3]) + " 의 내용이 바뀔 수 있습니다."
            return "함수 호출", text, ""

        if kind == "docstring":
            what = {"module": "이 모듈(파일)", "class": "이 클래스", "function": "이 함수"}.get(u.kind, "이 코드")
            return "독스트링", f"{what}이 무엇을 하는지 설명하는 문서 문자열입니다. 실행 결과에는 영향이 없습니다.", ""

        if kind == "expr":
            return "식 평가", f"{F(st.value, 60)} 식을 계산합니다. 결과는 사용되지 않습니다.", ""  # type: ignore[attr-defined]

        if kind == "return":
            v = st.value  # type: ignore[attr-defined]
            if v is None:
                return "반환", "값 없이 함수를 끝내고 호출한 곳으로 돌아갑니다 (`None` 반환).", ""
            if isinstance(v, ast.Tuple):
                return "반환", f"값 {len(v.elts)}개를 튜플로 묶어 호출한 곳으로 돌려주고 함수를 끝냅니다: {F(v, 60)}", ""
            return "반환", f"{val(v)} 을(를) 호출한 곳으로 돌려주고 함수를 끝냅니다.", ""

        if kind in ("if", "elif"):
            t = st.test  # type: ignore[attr-defined]
            if isinstance(t, ast.Compare) and isinstance(t.left, ast.Name) and t.left.id == "__name__":
                return "진입점 가드", "이 파일을 '직접 실행'했을 때만 아래 블록이 실행됩니다 (다른 파일에서 import 되면 실행되지 않음). 프로그램의 시작점입니다.", ""
            text = f"조건 {F(t, 60)} 이(가) 참이면 아래 블록을 실행합니다."
            if kind == "elif":
                text += " 앞선 조건이 모두 거짓일 때만 검사됩니다."
            return ("elif 분기" if kind == "elif" else "조건문 if"), text, self.cond_hint(fr, t)

        if kind == "for":
            it, tg = st.iter, F(st.target, 30)  # type: ignore[attr-defined]
            text = f"{F(it, 44)} 의 원소를 하나씩 꺼내 {tg} 에 담으며 아래 블록을 반복합니다."
            if isinstance(it, ast.Call):
                parts, _ = flatten_attr(it.func)
                last = parts[-1] if parts else ""
                a = [F(x, 16) for x in it.args]
                if last == "range" and len(parts) == 1 and a:
                    rng = f"0 이상 {a[0]} 미만" if len(a) == 1 else (f"{a[0]} 이상 {a[1]} 미만" if len(a) == 2 else f"{a[0]} 부터 {a[1]} 미만, 간격 {a[2]}")
                    text = f"정수 {rng} 를 하나씩 {tg} 에 담으며 아래 블록을 반복합니다 (정해진 횟수만큼)."
                elif last == "enumerate" and a:
                    text = f"{a[0]} 의 원소를 (번호, 값) 쌍으로 꺼내 {tg} 에 담으며 반복합니다."
                elif last == "zip":
                    text = f"여러 시퀀스({', '.join(a)})를 같은 위치끼리 묶어 {tg} 에 담으며 반복합니다 (가장 짧은 쪽에서 끝)."
                elif last == "items":
                    text = f"딕셔너리 {F(it.func.value, 30) if isinstance(it.func, ast.Attribute) else ''} 의 (키, 값) 쌍을 {tg} 에 담으며 반복합니다."
                elif last == "walk" and "os" in parts:
                    text = f"폴더 {a[0] if a else ''} 를 재귀적으로 내려가며 (현재폴더, 하위폴더들, 파일들)을 {tg} 에 담아 반복합니다."
            return "반복문 for", text, ""

        if kind == "while":
            t = st.test  # type: ignore[attr-defined]
            if isinstance(t, ast.Constant) and t.value is True:
                return "반복문 while", "무한 반복입니다. 블록 안의 `break`/`return`/예외로만 빠져나옵니다.", ""
            return "반복문 while", f"조건 {F(t, 60)} 이(가) 참인 동안 아래 블록을 계속 반복합니다. (조건을 바꾸는 코드가 없으면 무한 반복)", self.cond_hint(fr, t)

        if kind == "with":
            parts = []
            for it in st.items:  # type: ignore[attr-defined]
                s = F(it.context_expr, 40)
                if it.optional_vars is not None:
                    s += f" (→ {F(it.optional_vars, 20)})"
                parts.append(s)
            return "with 블록", f"{', '.join(parts)} 를 열어 블록 동안 사용하고, 블록이 끝나면(예외가 나도) 자동으로 정리·닫습니다.", ""

        if kind == "try":
            nh = len(st.handlers)  # type: ignore[attr-defined]
            text = f"예외가 발생할 수 있는 블록의 시작입니다. 예외가 나면 해당하는 `except`({nh}개)로 이동합니다."
            if st.finalbody:  # type: ignore[attr-defined]
                text += " 마지막에 `finally` 블록은 항상 실행됩니다."
            return "예외 처리 try", text, ""

        if kind == "except":
            if st.type is None:  # type: ignore[attr-defined]
                text = "모든 종류의 예외를 잡아서 처리합니다 (너무 넓은 범위라 원인 파악이 어려울 수 있음)."
            else:
                text = f"{F(st.type, 40)} 예외가 발생했을 때 실행됩니다."  # type: ignore[attr-defined]
            if st.name:  # type: ignore[attr-defined]
                text += f" 예외 객체는 `{st.name}` 에 담깁니다."  # type: ignore[attr-defined]
            return "예외 처리 except", text, ""

        if kind == "raise":
            e = st.exc  # type: ignore[attr-defined]
            if e is None:
                return "예외 발생", "처리 중이던 예외를 그대로 다시 발생시킵니다.", ""
            return "예외 발생", f"예외 {F(e, 50)} 를 발생시켜 현재 흐름을 중단합니다.", ""

        if kind == "assert":
            return "단언 assert", f"{F(st.test, 50)} 가 참이라고 단언합니다. 거짓이면 `AssertionError` 가 발생합니다.", ""  # type: ignore[attr-defined]
        if kind == "delete":
            return "삭제 del", f"{', '.join(F(t, 24) for t in st.targets)} 를 삭제합니다.", ""  # type: ignore[attr-defined]
        if kind == "global":
            kw = "global" if isinstance(st, ast.Global) else "nonlocal"
            return f"{kw} 선언", f"함수 안에서 바깥 변수 {', '.join('`' + n + '`' for n in st.names)} 를 직접 수정할 수 있게 선언합니다 ({kw}).", ""  # type: ignore[attr-defined]
        if kind == "pass":
            return "pass", "아무 동작도 하지 않는 자리표시자입니다.", ""
        if kind == "break":
            return "break", "가장 가까운 반복문을 즉시 탈출합니다.", ""
        if kind == "continue":
            return "continue", "이번 반복의 나머지를 건너뛰고 다음 반복으로 넘어갑니다.", ""
        if kind == "match":
            return "match 문", f"{F(st.subject, 40)} 의 모양에 따라 `case` 분기 중 하나를 실행합니다.", ""  # type: ignore[attr-defined]
        return "문장", short(fr.lines[st.lineno - 1].strip(), 80), ""  # type: ignore[attr-defined]

    # ────────── 토큰화(주석 + 구문 강조) ──────────
    def tokenize_file(self, fr: FileRec) -> None:
        toks = []
        try:
            for t in tokenize.generate_tokens(io.StringIO(fr.text).readline):
                toks.append(t)
        except (tokenize.TokenError, IndentationError, SyntaxError):
            pass
        fr.tokens = toks
        for t in toks:
            if t.type == tokenize.COMMENT:
                ln = t.start[0]
                standalone = 1 <= ln <= len(fr.lines) and fr.lines[ln - 1].strip().startswith("#")
                fr.comments[ln] = (t.string.lstrip("#").strip(), standalone)

    def build_segments(self, fr: FileRec) -> List[list]:
        if fr.lang != "py":
            return self.build_foreign_segments(fr)
        n = len(fr.lines)
        spans: List[list] = [[] for _ in range(n + 2)]
        prev = None
        skip_names = {"NEWLINE", "NL", "INDENT", "DEDENT", "ENDMARKER", "ENCODING"}
        for t in fr.tokens:
            name = tokenize.tok_name.get(t.type, "")
            if name in skip_names:
                continue
            s = t.string
            (sr, sc), (er, ec) = t.start, t.end
            cls = ""
            if t.type == tokenize.COMMENT:
                cls = "cmt"
            elif t.type == tokenize.STRING or name.startswith("FSTRING"):
                cls = "str"
            elif t.type == tokenize.NUMBER:
                cls = "num"
            elif t.type == tokenize.NAME:
                if keyword.iskeyword(s):
                    cls = "kw"
                elif prev == "def":
                    cls = "df"
                elif prev == "class":
                    cls = "cl"
                elif prev == "@":
                    cls = "dec"
                elif s in ("self", "cls"):
                    cls = "slf"
                elif s in BUILTINS:
                    cls = "bi"
            prev = s if s in ("def", "class", "@") else None
            sem = fr.sem.get((sr, sc)) if t.type == tokenize.NAME else None
            for r in range(sr, er + 1):
                if r > n:
                    break
                line_len = len(fr.lines[r - 1])
                start = sc if r == sr else 0
                end = ec if r == er else line_len
                end = min(end, line_len)
                if end > start:
                    spans[r].append((start, end, cls, sem if r == sr else None))
        out: List[list] = []
        for r in range(1, n + 1):
            line = fr.lines[r - 1]
            segs: List[list] = []
            cur = 0
            for (s0, e0, cls, sem) in sorted(spans[r], key=lambda x: (x[0], x[1])):
                if e0 <= cur:
                    continue
                if s0 < cur:
                    s0 = cur
                if s0 > cur:
                    segs.append([line[cur:s0]])
                text = line[s0:e0]
                if sem:
                    segs.append([text, cls] + list(sem))
                elif cls:
                    segs.append([text, cls])
                else:
                    segs.append([text])
                cur = e0
            if cur < len(line):
                segs.append([line[cur:]])
            out.append(segs)
        return out

    # ────────── 메트릭 / 요약 / 학습 순서 ──────────
    def compute_metrics(self, u: Unit) -> None:
        fr = self.files[u.file]
        c = u.cnt
        cc = 1 + c["if"] + c["for"] + c["while"] + c["except"] + c["boolop"] + c["ifexp"] + c["compif"] + c["comp"]
        code = 0
        for ln in range(u.line, min(u.end, len(fr.lines)) + 1):
            t = fr.lines[ln - 1].strip()
            if t and not fr.line_is_comment(ln):
                code += 1
        ncall = len([1 for e in u.callees.values() if e["k"] != "guess"])
        score = (u.end - u.line + 1) / 30.0 + cc * 0.55 + u.depth * 0.7 + c["calls"] * 0.08
        diff = 1 if score < 2 else 2 if score < 4 else 3 if score < 7 else 4 if score < 11 else 5
        u.metrics = {
            "lines": u.end - u.line + 1, "code": code, "cc": cc, "depth": u.depth,
            "calls": c["calls"], "branches": c["if"], "loops": c["for"] + c["while"],
            "excepts": c["except"], "returns": c["return"], "raises": c["raise"],
            "params": len(u.params), "callees": ncall, "callers": len(u.callers), "diff": diff,
        }

    def mark_cycles(self) -> None:
        n = len(self.units)
        index = [-1] * n
        low = [0] * n
        onstack = [False] * n
        stack: List[int] = []
        idx = 0
        in_cycle = [False] * n
        adj = [[t for t, e in u.callees.items() if e["k"] != "guess"] for u in self.units]
        for root in range(n):
            if index[root] != -1:
                continue
            work = [(root, 0)]
            while work:
                v, i = work.pop()
                if i == 0:
                    index[v] = low[v] = idx
                    idx += 1
                    stack.append(v)
                    onstack[v] = True
                recurse = False
                for k in range(i, len(adj[v])):
                    w = adj[v][k]
                    if index[w] == -1:
                        work.append((v, k + 1))
                        work.append((w, 0))
                        recurse = True
                        break
                    elif onstack[w]:
                        low[v] = min(low[v], index[w])
                if recurse:
                    continue
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = stack.pop()
                        onstack[w] = False
                        comp.append(w)
                        if w == v:
                            break
                    if len(comp) > 1:
                        for w in comp:
                            in_cycle[w] = True
                if work:
                    parent = work[-1][0]
                    low[parent] = min(low[parent], low[v])
        for u in self.units:
            e = u.callees.get(u.id)
            u.is_recursive = bool(e and e["k"] == "call")
            u.in_cycle = in_cycle[u.id]  # type: ignore[attr-defined]

    def compute_flags(self, u: Unit) -> None:
        if u.kind == "module":
            u.is_entry = bool(u.callees)
            return
        if u.kind != "function":
            return
        if not u.callers and (u.callees or u.name == "main") and not u.name.startswith(("visit_", "__")):
            u.is_entry = True
        if (not u.callers and not u.decos and not u.name.startswith(("__", "test", "visit_", "on_", "do_"))
                and u.name != "main" and self.files[u.file].module_unit is not None
                and not self.files[u.file].rel.endswith("__init__.py")):
            ok = True
            if u.cls is not None:
                nb = len(u.cls.node.bases)  # type: ignore[attr-defined]
                if nb > len(self.class_bases.get(u.cls.id, [])):
                    ok = False  # 외부 부모 클래스(프레임워크 콜백일 수 있음)
            u.is_dead = ok

    def static_summary(self, u: Unit) -> dict:
        fr = self.files[u.file]
        bul: List[str] = []
        if u.kind == "module":
            funcs = [c for c in u.children if c.kind == "function"]
            classes = [c for c in u.children if c.kind == "class"]
            one = (u.doc.split("\n")[0] if u.doc else
                   f"{fr.rel} — 함수 {len(funcs)}개 · 클래스 {len(classes)}개" + (" · 실행 코드 있음" if u.callees else ""))
            if classes:
                bul.append("클래스: " + ", ".join(f"`{c.name}`" for c in classes[:8]))
            if funcs:
                bul.append("함수: " + ", ".join(f"`{c.name}`" for c in funcs[:10]) + (" …" if len(funcs) > 10 else ""))
            if u.callees:
                bul.append("모듈 실행부(최상위 코드)가 파일을 불러올 때 바로 실행됩니다: " + ", ".join(
                    f"`{self.units[t].disp}`" for t in list(u.callees)[:6]))
            deps = [self.files[d].rel for d in sorted(fr.deps)][:6]
            if deps:
                bul.append("내부 의존 파일: " + ", ".join(f"`{d}`" for d in deps))
            ext = sorted({a[1].split(".")[0] if a[0] == "mod" else a[1].split(".")[0] for a in u.aliases.values()
                          if (a[0] == "mod" and self.find_module(a[1]) is None) or (a[0] == "from" and self.find_module(a[1]) is None and a[1])})
            if ext:
                bul.append("외부 라이브러리: " + ", ".join(f"`{e}`" for e in ext[:10]))
            return {"one": clamp_sentences(one, 140), "bul": bul}
        if u.kind == "class":
            meths = [c for c in u.children if c.kind == "function"]
            bases = [b.name for b in self.class_bases.get(u.id, [])]
            raw_bases = [short(fr.seg(b), 24) for b in u.node.bases] if (fr.lang == "py" and isinstance(u.node, ast.ClassDef)) else []
            one = u.doc.split("\n")[0] if u.doc else f"클래스 `{u.name}` — 메서드 {len(meths)}개"
            if raw_bases:
                bul.append("상속: " + ", ".join(f"`{b}`" for b in raw_bases))
            if meths:
                bul.append("메서드: " + ", ".join(f"`{m.name}`" for m in meths[:12]) + (" …" if len(meths) > 12 else ""))
            if u.attrs:
                bul.append("인스턴스/클래스 속성: " + ", ".join(f"`{k}`" for k in list(u.attrs)[:10]))
            return {"one": clamp_sentences(one, 140), "bul": bul}
        # function
        pnames = [p for p in u.params if p["name"] != u.self_name]
        ptxt = ", ".join(p["name"] + (f": {p['ann']}" if p["ann"] else "") for p in pnames[:20]) or "없음"
        if len(pnames) > 20:
            ptxt += f" 외 {len(pnames) - 20}개"
        yields = u.cnt["yield"] > 0
        if fr.lang == "matlab":
            ret_vars = [x.strip() for x in (u.ret_ann or "").split(",") if x.strip()]
            if ret_vars:
                rtxt = ", ".join(f"`{v}`" for v in ret_vars[:20]) + (f" 외 {len(ret_vars) - 20}개" if len(ret_vars) > 20 else "")
            elif u.rets and u.rets != ["None"]:
                rtxt = ", ".join(f"`{r}`" for r in u.rets[:3])
            else:
                rtxt = "없음(void)"
        elif fr.lang in ("c", "cpp"):
            if u.ret_ann == "void" and not u.rets:
                rtxt = "없음(void)"
            elif u.rets:
                rtxt = ", ".join(f"`{r}`" for r in u.rets[:3]) + (f" (반환형 `{u.ret_ann}`)" if u.ret_ann else "")
            elif u.ret_ann:
                rtxt = f"반환형 `{u.ret_ann}`"
            else:
                rtxt = "없음(void)"
        elif fr.lang in ("js", "ts", "tsx"):
            if u.rets:
                rtxt = ", ".join(f"`{r}`" for r in u.rets[:3]) + (f" (타입 `{u.ret_ann}`)" if u.ret_ann else "")
            elif u.ret_ann:
                rtxt = "없음(void)" if u.ret_ann == "void" else f"타입 `{u.ret_ann}`"
            else:
                rtxt = "없음(undefined)"
        else:
            if yields:
                rtxt = "제너레이터(값을 하나씩 yield)"
            elif u.rets and u.rets != ["None"]:
                rtxt = ", ".join(f"`{r}`" for r in u.rets[:3])
            else:
                rtxt = "없음(None)"
            if u.ret_ann:
                rtxt += f" · 표기 타입 `{u.ret_ann}`"
        if u.doc:
            one = u.doc.split("\n")[0]
        else:
            one = f"입력 {ptxt} → 출력 {rtxt.replace('`', '')}"
        bul.append(f"입력: {ptxt}")
        bul.append(f"출력: {rtxt}")
        flow = []
        m = u.metrics
        if m["branches"]:
            flow.append(f"분기 {m['branches']}개")
        if m["loops"]:
            flow.append(f"반복 {m['loops']}개")
        if m["excepts"]:
            flow.append(f"예외처리 {m['excepts']}개")
        if m["depth"] >= 3:
            flow.append(f"중첩 깊이 {m['depth']}")
        bul.append("흐름: " + (" · ".join(flow) if flow else "분기·반복 없이 위에서 아래로 순차 실행") + f" (복잡도 {m['cc']}, {m['lines']}줄)")
        ins = sorted(((e["lines"][0] if e["lines"] else 0, t) for t, e in u.callees.items() if e["k"] == "call"))
        if ins:
            bul.append("내부 호출: " + ", ".join(f"`{self.units[t].disp}`" for _, t in ins[:6]) + (" …" if len(ins) > 6 else ""))
        ext = u.ext_calls.most_common(4)
        if ext:
            ext_parts = []
            for c, _ in ext:
                meaning = KB_CALLS.get(c) or KB_FOREIGN.get(c) or KB_FOREIGN.get(c.split(".")[-1].split("::")[-1], "")
                ext_parts.append(f"`{c}`" + (f"({meaning})" if meaning else ""))
            bul.append("외부 호출: " + ", ".join(ext_parts))
        if u.effects:
            bul.append("부작용: " + ", ".join(EFFECT_LABELS[e] for e in sorted(u.effects)))
        if u.globals_declared:
            bul.append("전역 변수 수정: " + ", ".join(f"`{g}`" for g in sorted(u.globals_declared)))
        attrs = [k for k, v in u.vars.items() if k.startswith("self.") and v["defs"]]
        if attrs:
            bul.append("객체 상태 변경: " + ", ".join(f"`{a}`" for a in attrs[:6]))
        if u.is_recursive:
            bul.append("자기 자신을 호출하는 재귀 함수입니다.")
        return {"one": clamp_sentences(one, 360), "bul": bul}

    def compute_steps(self, u: Unit) -> None:
        """함수/모듈 본문을 2~6개의 논리 단계(Step)로 묶어 맥락 단위 학습 구조를 만든다."""
        if u.kind not in ("function", "module"):
            return
        body = list(getattr(u.node, "body", None) or [])
        if not body:
            return
        fr = self.files[u.file]
        if isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Constant) and isinstance(body[0].value.value, str):
            body = body[1:]
        if not body:
            return

        def st_span(st: ast.AST) -> Tuple[int, int]:
            a = getattr(st, "lineno", 1)
            decos = getattr(st, "decorator_list", None) or []
            if decos:
                a = min([a] + [getattr(d, "lineno", a) for d in decos])
            z = getattr(st, "end_lineno", a) or a
            return a, z

        def st_cat(st: ast.AST) -> str:
            a, z = st_span(st)
            if isinstance(st, (ast.Import, ast.ImportFrom)):
                return "import"
            if isinstance(st, SCOPE_TYPES):
                return "def"
            if isinstance(st, LOOP_TYPES):
                return "loop"
            if isinstance(st, TRY_TYPES):
                return "try"
            if isinstance(st, (ast.With, ast.AsyncWith)):
                return "with"
            if isinstance(st, ast.If):
                exits = (ast.Return, ast.Raise, ast.Continue, ast.Break)
                if len(st.body) <= 2 and not st.orelse and any(isinstance(b, exits) for b in st.body) and (z - a + 1) <= 4:
                    return "guard"
                return "if"
            if isinstance(st, ast.Return):
                return "return"
            if isinstance(st, ast.Raise):
                return "raise"
            if isinstance(st, ast.Expr) and isinstance(st.value, ast.Call):
                return "call"
            return "assign"

        def clean_cmt(ln: int) -> str:
            c = fr.comments.get(ln)
            if not c or not c[1]:
                return ""
            txt = re.sub(r"^[\s\-─=*#·]+|[\s\-─=*#·]+$", "", c[0]).strip()
            return txt if len(txt) >= 2 and re.search(r"[가-힣A-Za-z0-9]", txt) else ""

        groups: List[List[ast.AST]] = []
        cur: List[ast.AST] = []
        cur_start = 0
        prev_z = 0
        prev_cat = ""
        prev_big_if = False

        for st in body:
            a, z = st_span(st)
            cat = st_cat(st)
            big_if = (cat == "if") and ((z - a + 1) >= 3 or bool(getattr(st, "orelse", None)))
            has_cmt = any(clean_cmt(ln) for ln in range(max(prev_z + 1, a - 2), a))
            split = False
            if cur:
                if has_cmt:
                    split = True
                elif cat in ("loop", "try", "with", "def") and not (cat == "def" and prev_cat == "def"):
                    split = True
                elif prev_cat in ("loop", "try", "with", "def") and not (cat == "def" and prev_cat == "def"):
                    split = True
                elif big_if or prev_big_if:
                    split = True
                elif (cat == "guard") != (prev_cat == "guard"):
                    split = True
                elif (cat == "import") != (prev_cat == "import"):
                    split = True
                elif cat == "return" and (len(cur) >= 2 or (a - cur_start) >= 4 or prev_cat not in ("assign", "call")):
                    split = True
                elif cat != "def" and ((z - cur_start + 1) > 12 or len(cur) >= 5):
                    split = True
            if split:
                groups.append(cur)
                cur = []
            if not cur:
                cur_start = a
            cur.append(st)
            prev_z = z
            prev_cat = cat
            prev_big_if = big_if
        if cur:
            groups.append(cur)

        def grp_span(g: List[ast.AST]) -> Tuple[int, int]:
            return min(st_span(s)[0] for s in g), max(st_span(s)[1] for s in g)

        while len(groups) > 6:
            best_i = 0
            best_score = 10 ** 9
            for i in range(len(groups) - 1):
                g1, g2 = groups[i], groups[i + 1]
                a1, z1 = grp_span(g1)
                a2, z2 = grp_span(g2)
                c1 = {st_cat(s) for s in g1}
                c2 = {st_cat(s) for s in g2}
                pen = 0
                if ("def" in c1) != ("def" in c2):
                    pen += 100
                if c1 & {"loop", "try", "with"} and c2 & {"loop", "try", "with"}:
                    pen += 40
                score = (z2 - a1 + 1) + pen
                if score < best_score:
                    best_score = score
                    best_i = i
            groups[best_i] = groups[best_i] + groups[best_i + 1]
            groups.pop(best_i + 1)

        param_names = {p["name"] for p in u.params if p["name"] != u.self_name}
        steps: List[dict] = []
        for idx, grp in enumerate(groups, start=1):
            l1, l2 = grp_span(grp)
            reads: List[str] = []
            writes: List[str] = []
            muts: List[str] = []
            calls: List[list] = []
            seen_call: set = set()
            cats = [st_cat(s) for s in grp]

            for ln in range(l1, l2 + 1):
                inf = fr.info.get(ln)
                if not inf or inf.get("k") in ("cont", "blank", "comment"):
                    continue
                for r in inf.get("r") or []:
                    if r not in reads:
                        reads.append(r)
                for w in inf.get("w") or []:
                    if w not in writes:
                        writes.append(w)
                for m in inf.get("m") or []:
                    if m not in muts:
                        muts.append(m)
                for c in inf.get("c") or []:
                    if c and c[0] not in seen_call:
                        seen_call.add(c[0])
                        calls.append(c)

            from_earlier: List[str] = []
            for r in reads:
                if r == u.self_name:
                    continue
                v = u.vars.get(r)
                if r in param_names or (v and any(d[0] < l1 for d in v.get("defs", []))):
                    from_earlier.append(r)

            used_later: List[str] = []
            for w in writes + [m for m in muts if m not in writes]:
                if w.startswith("self."):
                    used_later.append(w)
                    continue
                v = u.vars.get(w)
                if v and any(us > l2 for us in v.get("uses", [])):
                    used_later.append(w)

            cmt_title = ""
            for ln in range(max(u.line, l1 - 2), l1):
                c_txt = clean_cmt(ln)
                if c_txt:
                    cmt_title = short(c_txt, 34)

            first_call = calls[0][0].rstrip("()") if calls else ""
            if cmt_title:
                title = cmt_title
            elif all(c == "import" for c in cats):
                title = "모듈 불러오기"
            elif all(c == "def" for c in cats):
                title = "보조 함수·클래스 정의"
            elif all(c == "guard" for c in cats):
                title = "입력·조건 가드 검사"
            elif "try" in cats:
                title = "예외 처리 블록"
            elif "loop" in cats:
                title = f"반복 처리 ({first_call})" if first_call else "반복 순회 처리"
            elif "with" in cats:
                title = "자원 열기·컨텍스트 처리"
            elif "if" in cats:
                title = "조건 분기 처리"
            elif cats[-1] == "return" and len(cats) <= 2:
                title = "결과 정리 및 반환"
            elif idx == 1 and all(c in ("assign", "call") for c in cats):
                title = "초기 변수·상태 준비"
            elif first_call:
                title = f"{short(first_call, 24)} 호출 및 처리"
            else:
                title = "핵심 값 계산·갱신"

            parts_desc: List[str] = []
            if "import" in cats:
                parts_desc.append("필요한 모듈과 도구를 불러옵니다.")
            if "def" in cats:
                defs_n = [getattr(s, "name", "") for s in grp if isinstance(s, SCOPE_TYPES)]
                parts_desc.append(f"내부 블록에서 사용할 `{', '.join(defs_n[:4])}` 등을 정의합니다.")
            if all(c == "guard" for c in cats):
                parts_desc.append("본격적인 처리에 들어가기 전에 조건이 맞지 않으면 함수를 일찍 빠져나오거나 예외를 발생시킵니다.")
            if "loop" in cats:
                loop_iters = [short(fr.seg(s.iter), 32) for s in grp if isinstance(s, (ast.For, ast.AsyncFor))]  # type: ignore[attr-defined]
                if loop_iters:
                    parts_desc.append(f"`{loop_iters[0]}` 을(를) 순회하면서 조건 확인과 값 갱신을 반복합니다.")
                else:
                    parts_desc.append("종료 조건이 만족될 때까지 반복 실행하며 상태를 갱신합니다.")
            if "if" in cats:
                conds = [short(fr.seg(s.test), 32) for s in grp if isinstance(s, ast.If)]
                if conds:
                    parts_desc.append(f"조건(`{conds[0]}`) 결과에 따라 실행 경로를 나눕니다.")
            if "try" in cats:
                parts_desc.append("실행 중 오류가 날 수 있는 작업을 시도하고, 예외 발생 시 안전하게 대응합니다.")
            if "with" in cats:
                parts_desc.append("파일·잠금·네트워크 등의 자원을 열고 블록이 끝나면 자동으로 정리합니다.")
            if writes:
                parts_desc.append(f"`{', '.join(writes[:4])}`" + (" 등" if len(writes) > 4 else "") + "에 계산 결과를 저장합니다.")
            if calls:
                clabs = ", ".join(f"`{c[0]}`" for c in calls[:3])
                parts_desc.append(f"{clabs} 호출을 통해 핵심 작업을 수행합니다.")
            if cats[-1] == "return":
                parts_desc.append("최종 결과를 호출한 쪽으로 반환하며 실행을 마칩니다.")
            if not parts_desc:
                parts_desc.append(f"L{l1}~L{l2}의 {len(grp)}개 문장을 순서대로 실행합니다.")

            why_parts: List[str] = []
            if from_earlier:
                why_parts.append(f"앞선 단계(또는 입력)의 `{', '.join(from_earlier[:4])}` 을(를) 받아")
            if used_later:
                why_parts.append(f"이후 단계에서 쓰일 `{', '.join(used_later[:4])}` 상태를 준비합니다.")
            elif cats[-1] == "return":
                why_parts.append("이 함수가 만들어야 할 최종 결과값을 완성해 돌려줍니다.")
            elif muts:
                why_parts.append(f"`{', '.join(muts[:3])}` 의 내용을 직접 갱신해 다음 흐름에 반영합니다.")
            elif calls:
                why_parts.append(f"`{calls[0][0]}` 호출로 다음 단계를 진행하거나 부작용(출력/저장 등)을 수행합니다.")
            else:
                why_parts.append("함수 전체 목표를 이루기 위한 중간 계산 단계입니다.")

            steps.append({
                "id": idx, "l1": l1, "l2": l2, "t": title,
                "d": " ".join(parts_desc),
                "w": " ".join(why_parts),
                "r": from_earlier[:8],
                "wr": writes[:8],
                "ul": used_later[:8],
                "c": [[c[0], c[1], c[2], short(c[3], 60)] for c in calls[:6]],
            })
        u.steps = steps

    def learning_order(self) -> dict:
        def first_line(t: Unit, s: Unit) -> int:
            e = s.callees[t.id]
            return min(e["lines"]) if e["lines"] else 10 ** 9

        def kids(s: Unit) -> List[Unit]:
            ks = [self.units[t] for t, e in s.callees.items() if e["k"] != "guess" and self.units[t].kind == "function"]
            ks.sort(key=lambda t: first_line(t, s))
            return ks

        entries = [u for u in self.units if u.is_entry]
        entries.sort(key=lambda u: (0 if u.kind == "module" and u.callees and any(
            "__main__" in l for l in self.files[u.file].lines) else 1,
            0 if u.name == "main" else 1, u.file, u.line))
        down: List[int] = []
        up: List[int] = []
        why: Dict[int, str] = {}
        seen: set = set()

        def dfs(s: Unit, parent: Optional[Unit]) -> None:
            stack = [(s, parent, iter(kids(s)))]
            seen.add(s.id)
            if s.kind != "module" or s.callees:
                down.append(s.id)
            why[s.id] = "진입점 (호출하는 곳 없음)" if parent is None else f"`{parent.disp}` 가 호출"
            while stack:
                cur, par, it = stack[-1]
                nxt = next(it, None)
                if nxt is None:
                    stack.pop()
                    if cur.kind != "module" or cur.callees:
                        up.append(cur.id)
                    continue
                if nxt.id in seen:
                    continue
                seen.add(nxt.id)
                down.append(nxt.id)
                why[nxt.id] = f"`{cur.disp}` 가 호출"
                stack.append((nxt, cur, iter(kids(nxt))))

        for e in entries:
            if e.id not in seen:
                dfs(e, None)
        for u in self.units:
            if u.kind == "function" and u.id not in seen:
                down.append(u.id)
                up.append(u.id)
                why[u.id] = "다른 함수에서 직접 호출되지 않음 (콜백/외부 호출/미사용 가능)"
        return {"down": down, "up": up, "why": why}

    # ────────── 전체 분석 파이프라인 ──────────
    def analyze(self, progress: Optional[Callable[[str, int, int], None]] = None) -> None:
        def prog(msg: str, i: int = 0, n: int = 0) -> None:
            if progress:
                progress(msg, i, n)
        self.load()
        for fr in self.files:
            if fr.lang == "py":
                self.tokenize_file(fr)
                self.build_units(fr)
            else:
                self.tokenize_foreign_comments(fr)
                self.build_foreign_units(fr)
        self.build_modmap()
        for fr in self.files:
            if fr.lang == "py":
                for imp in fr.imports_all:
                    f = self.find_module(imp)
                    if f is not None and f != fr.idx:
                        fr.deps.add(f)
        self.resolve_foreign_deps()
        for u in self.units:
            if self.files[u.file].lang == "py":
                self.prepare_unit(u)
        self.compute_class_info()
        total = len(self.units)
        for i, u in enumerate(self.units):
            if self.files[u.file].lang == "py":
                self.analyze_scope(u)
            else:
                self.analyze_foreign_scope(u)
            if i % 50 == 0:
                prog("정적 분석", i, total)
        # 클래스 속성 요약
        for u in self.units:
            if u.kind == "class":
                for k, v in u.vars.items():
                    if v["kind"] in ("local", "def") and v["defs"] and not k.startswith("self."):
                        u.attrs[k] = {"type": v["type"], "where": "클래스 변수", "line": v["defs"][0][0]}
                for m in u.children:
                    if m.kind != "function":
                        continue
                    for k, v in m.vars.items():
                        if k.startswith("self.") and v["defs"]:
                            a = k[5:]
                            cur = u.attrs.setdefault(a, {"type": "", "where": f"`{m.name}` 에서 설정", "line": v["defs"][0][0]})
                            if not cur["type"]:
                                t = v["type"] or (self.class_attr_types.get(u.id, {}).get(a).name  # type: ignore[union-attr]
                                                  if self.class_attr_types.get(u.id, {}).get(a) else "")
                                cur["type"] = t
        for u in self.units:
            is_foreign = self.files[u.file].lang != "py"
            for tid, e in u.callees.items():
                self.units[tid].callers[u.id] = {"k": e["k"], "lines": e["lines"]}
                if is_foreign and e["k"] != "guess" and self.units[tid].file != u.file:
                    self.files[u.file].deps.add(self.units[tid].file)
        self.mark_cycles()
        for u in self.units:
            self.compute_metrics(u)
            self.compute_flags(u)
        for u in self.units:
            u.static = self.static_summary(u)
            if self.files[u.file].lang == "py":
                self.compute_steps(u)
        self.order = self.learning_order()
        # 줄 → 단위 매핑 (주석·빈 줄 등 문장 밖의 줄에 사용)
        for fr in self.files:
            lu: Dict[int, int] = {}
            for u in self.units:
                if u.file == fr.idx and u.kind in ("function", "class"):
                    for ln in range(u.line, u.end + 1):
                        lu[ln] = u.id
            base = fr.module_unit.id  # type: ignore[union-attr]
            n = len(fr.lines)
            for ln in range(1, n + 1):
                if ln in fr.info:
                    continue
                uid = lu.get(ln, base)
                t = fr.lines[ln - 1].strip()
                if not t:
                    fr.info[ln] = {"k": "blank", "u": uid}
                elif fr.line_is_comment(ln):
                    nxt = ln + 1
                    while nxt <= n and fr.line_is_comment(nxt):
                        nxt += 1
                    txt_c = re.sub(r"^[/\*%#\s]+|[\*/\s]+$", "", t).strip()
                    fr.info[ln] = {"k": "comment", "u": uid, "t": "주석", "x": txt_c or "(빈 주석)", "n": nxt}
                else:
                    fr.info[ln] = {"k": "syntax", "u": uid, "t": "구문", "x": f"`{short(t, 60)}` — 블록의 시작/끝 괄호 또는 문장의 일부입니다."}
        prog("정적 분석 완료", total, total)


def self_parent_body0(proj: "Project", fr: FileRec, st: ast.AST) -> bool:
    par = fr.parents.get(id(st))
    body = getattr(par, "body", None)
    return isinstance(par, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and \
        isinstance(body, list) and body and body[0] is st


# ═════════════════════════════════════════════════════════════════════════════
#  LLM 방어 계층
#  - LLM 은 '함수 요약 문장'만 담당하고 구조/해설은 전부 정적 분석이 담당한다.
#  - 작은 프롬프트(함수 1개) · 태그 줄 형식(JSON 아님) · 전수 검증 · 캐시 · 차단기(circuit breaker)
# ═════════════════════════════════════════════════════════════════════════════
class LLMError(Exception):
    def __init__(self, msg: str, transport: bool = True):
        super().__init__(msg)
        self.transport = transport


class LLMClient:
    """OpenAI 호환 /chat/completions 클라이언트 (urllib 만 사용, 특정 모델에 종속되지 않음)."""

    def __init__(self, base_url: str, api_key: str = "", model: str = "", timeout: int = 90,
                 extra_body: Optional[dict] = None):
        self.base_url = (base_url or "").rstrip("/")
        self.api_key = (api_key or "").strip() or "sk-no-key-required"
        self.model = (model or "").strip()
        self.timeout = timeout
        self.extra_body = extra_body or {}

    def _headers(self) -> dict:
        return {"Content-Type": "application/json", "Authorization": f"Bearer {self.api_key}"}

    def _ssl_ctx(self):
        import ssl
        ctx = ssl.create_default_context()
        ctx.verify_flags &= ~getattr(ssl, "VERIFY_X509_STRICT", 0)
        return ctx

    def list_models(self, timeout: int = 6) -> List[str]:
        req = urllib.request.Request(self.base_url + "/models", headers=self._headers(), method="GET")
        with urllib.request.urlopen(req, timeout=timeout, context=self._ssl_ctx()) as resp:
            body = json.loads(resp.read().decode("utf-8", "replace"))
        return [m.get("id", "") for m in body.get("data", []) if isinstance(m, dict) and m.get("id")]

    def complete(self, system: str, user: str, max_tokens: int = 600) -> Tuple[str, str]:
        return self.complete_messages(
            [{"role": "system", "content": system}, {"role": "user", "content": user}],
            max_tokens=max_tokens, temperature=0.1,
        )

    def complete_messages(self, messages: List[Dict[str, str]], max_tokens: int = 900,
                          temperature: float = 0.2) -> Tuple[str, str]:
        payload = {
            "model": self.model,
            "messages": messages,
            "temperature": temperature,
            "max_tokens": max_tokens,
            "stream": False,
        }
        payload.update(self.extra_body)
        req = urllib.request.Request(self.base_url + "/chat/completions",
                                     data=json.dumps(payload).encode("utf-8"),
                                     headers=self._headers(), method="POST")
        try:
            with urllib.request.urlopen(req, timeout=self.timeout, context=self._ssl_ctx()) as resp:
                body = json.loads(resp.read().decode("utf-8", "replace"))
        except urllib.error.HTTPError as e:
            detail = ""
            try:
                detail = e.read().decode("utf-8", "replace")[:160]
            except Exception:
                pass
            raise LLMError(f"HTTP {e.code} {detail}")
        except (urllib.error.URLError, TimeoutError, OSError, ValueError) as e:
            raise LLMError(f"연결/시간초과: {e}")
        try:
            ch = body["choices"][0]
            content = (ch.get("message") or {}).get("content") or ch.get("text") or ""
            finish = ch.get("finish_reason") or ""
        except (KeyError, IndexError, TypeError, AttributeError):
            raise LLMError("응답 형식이 OpenAI 호환이 아닙니다", transport=False)
        if not content.strip():
            raise LLMError("빈 응답 (추론만 하다 토큰이 끝났을 수 있음)", transport=False)
        return content, finish

    def preflight(self, log: Callable[[str], None]) -> bool:
        try:
            ids = self.list_models()
            if not self.model and ids:
                self.model = ids[0]
                log(f"  [LLM] 모델명이 비어 있어 서버의 첫 모델을 사용합니다: {self.model}")
            elif ids and self.model not in ids:
                log(f"  [LLM] 주의: 서버 모델 목록에 '{self.model}' 이(가) 없습니다 (목록: {', '.join(ids[:4])})")
        except Exception as e:
            log(f"  [LLM] /models 조회 실패(무시하고 진행): {e}")
        if not self.model:
            log("  [LLM] 모델명을 알 수 없어 AI 해설을 건너뜁니다. (설정에서 모델명을 입력하세요)")
            return False
        try:
            txt, _ = self.complete("한 단어로만 답하라.", "OK 라고만 답하라.", max_tokens=24)
            log(f"  [LLM] 연결 확인 완료 (응답: {short(clean_llm_text(txt), 20)})")
            return True
        except LLMError as e:
            log(f"  [LLM] 연결 확인 실패 → AI 해설 없이 정적 분석만 사용합니다: {e}")
            return False


_TEX_MAP = [
    (re.compile(r"(?:\\|\|)(?:rightarrow|rightattow|longrightarrow|to)\b"), "→"),
    (re.compile(r"(?:\\|\|)(?:leftarrow|longleftarrow|gets)\b"), "←"),
    (re.compile(r"(?:\\|\|)(?:leftrightarrow|longleftrightarrow)\b"), "↔"),
    (re.compile(r"(?:\\|\|)(?:Rightarrow|implies)\b"), "⇒"),
    (re.compile(r"(?:\\|\|)(?:Leftarrow)\b"), "⇐"),
    (re.compile(r"(?:\\|\|)(?:leq|le)\b"), "≤"),
    (re.compile(r"(?:\\|\|)(?:geq|ge)\b"), "≥"),
    (re.compile(r"(?:\\|\|)(?:neq|ne)\b"), "≠"),
    (re.compile(r"(?:\\|\|)(?:approx|simeq|sim)\b"), "≈"),
    (re.compile(r"(?:\\|\|)equiv\b"), "≡"),
    (re.compile(r"(?:\\|\|)pm\b"), "±"),
    (re.compile(r"(?:\\|\|)mp\b"), "∓"),
    (re.compile(r"(?:\\|\|)infty\b"), "∞"),
    (re.compile(r"(?:\\|\|)partial\b"), "∂"),
    (re.compile(r"(?:\\|\|)nabla\b"), "∇"),
    (re.compile(r"(?:\\|\|)sum\b"), "∑"),
    (re.compile(r"(?:\\|\|)prod\b"), "∏"),
    (re.compile(r"(?:\\|\|)int\b"), "∫"),
    (re.compile(r"(?:\\|\|)notin\b"), "∉"),
    (re.compile(r"(?:\\|\|)in\b"), "∈"),
    (re.compile(r"(?:\\|\|)subseteq\b"), "⊆"),
    (re.compile(r"(?:\\|\|)subset\b"), "⊂"),
    (re.compile(r"(?:\\|\|)forall\b"), "∀"),
    (re.compile(r"(?:\\|\|)exists\b"), "∃"),
    (re.compile(r"(?:\\|\|)propto\b"), "∝"),
    (re.compile(r"(?:\\|\|)times\b"), "×"),
    (re.compile(r"(?:\\|\|)cdot\b"), "·"),
    (re.compile(r"(?:\\|\|)(?:ldots|cdots|dots)\b"), "…"),
    (re.compile(r"(?:\\|\|)(?:varepsilon|epsilon)\b"), "ε"),
    (re.compile(r"(?:\\|\|)alpha\b"), "α"),
    (re.compile(r"(?:\\|\|)beta\b"), "β"),
    (re.compile(r"(?:\\|\|)gamma\b"), "γ"),
    (re.compile(r"(?:\\|\|)delta\b"), "δ"),
    (re.compile(r"(?:\\|\|)zeta\b"), "ζ"),
    (re.compile(r"(?:\\|\|)eta\b"), "η"),
    (re.compile(r"(?:\\|\|)(?:vartheta|theta)\b"), "θ"),
    (re.compile(r"(?:\\|\|)iota\b"), "ι"),
    (re.compile(r"(?:\\|\|)kappa\b"), "κ"),
    (re.compile(r"(?:\\|\|)lambda\b"), "λ"),
    (re.compile(r"(?:\\|\|)mu\b"), "μ"),
    (re.compile(r"(?:\\|\|)nu\b"), "ν"),
    (re.compile(r"(?:\\|\|)xi\b"), "ξ"),
    (re.compile(r"(?:\\|\|)pi\b"), "π"),
    (re.compile(r"(?:\\|\|)(?:varrho|rho)\b"), "ρ"),
    (re.compile(r"(?:\\|\|)(?:varsigma|sigma)\b"), "σ"),
    (re.compile(r"(?:\\|\|)tau\b"), "τ"),
    (re.compile(r"(?:\\|\|)upsilon\b"), "υ"),
    (re.compile(r"(?:\\|\|)(?:varphi|phi)\b"), "φ"),
    (re.compile(r"(?:\\|\|)chi\b"), "χ"),
    (re.compile(r"(?:\\|\|)psi\b"), "ψ"),
    (re.compile(r"(?:\\|\|)omega\b"), "ω"),
    (re.compile(r"(?:\\|\|)Gamma\b"), "Γ"),
    (re.compile(r"(?:\\|\|)Delta\b"), "Δ"),
    (re.compile(r"(?:\\|\|)Theta\b"), "Θ"),
    (re.compile(r"(?:\\|\|)Lambda\b"), "Λ"),
    (re.compile(r"(?:\\|\|)Xi\b"), "Ξ"),
    (re.compile(r"(?:\\|\|)Pi\b"), "Π"),
    (re.compile(r"(?:\\|\|)Sigma\b"), "Σ"),
    (re.compile(r"(?:\\|\|)Phi\b"), "Φ"),
    (re.compile(r"(?:\\|\|)Psi\b"), "Ψ"),
    (re.compile(r"(?:\\|\|)Omega\b"), "Ω"),
]


def _unwrap_tex_dollar(m: re.Match) -> str:
    inner = m.group(1).strip()
    if not inner:
        return ""
    if re.fullmatch(r"[\d,.]+", inner):
        return m.group(0)
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.\[\]()]*", inner):
        return f"`{inner}`"
    return inner


def sanitize_tex(t: str) -> str:
    for rx, rep in _TEX_MAP:
        t = rx.sub(rep, t)
    t = re.sub(r"(?:\\|\|)(?:left|right)\b", "", t)
    t = re.sub(r"(?:\\|\|)frac\{([^{}]+)\}\{([^{}]+)\}", r"(\1)/(\2)", t)
    t = re.sub(r"(?:\\|\|)sqrt\{([^{}]+)\}", r"√(\1)", t)
    t = re.sub(r"(?:\\|\|)(?:text|mathrm|mathbf|mathit|mathcal|operatorname|hat|bar|tilde|vec|dot)\{([^{}]+)\}", r"\1", t)
    t = re.sub(r"([_^])\{([^{}]{1,24})\}", r"\1\2", t)
    t = re.sub(r"\$\$([^$\n]{1,200})\$\$", _unwrap_tex_dollar, t)
    t = re.sub(r"\$([^$\n]{1,120})\$", _unwrap_tex_dollar, t)
    return t


def clean_llm_text(raw: str, keep_md: bool = False) -> str:
    t = raw or ""
    t = re.sub(r"<think>.*?</think>", "", t, flags=re.S | re.I)
    if re.search(r"</think>", t, re.I):          # 여는 태그가 템플릿에 포함된 모델
        t = re.split(r"</think>", t, flags=re.I)[-1]
    if re.search(r"<think>", t, re.I):           # 닫히지 않은 추론
        t = re.split(r"<think>", t, flags=re.I)[0]
    t = re.sub(r"^\s*```[A-Za-z]*\s*$", "", t, flags=re.M)
    t = sanitize_tex(t)
    if not keep_md:
        t = t.replace("**", "")
    return t.strip()


FIELD_RE = re.compile(r"^\s*(?:[-*•>#]+\s*)*(요약|역할|주의|개요|흐름)\s*[:：]\s*(.*)$")
LINE_RE = re.compile(r"^\s*(?:[-*•]\s*)?(?:L|l|Line|line|줄|라인)?\s*(\d{1,6})\s*(?:번째\s*줄|번\s*줄|줄|번)?\s*[:：.)\]\-]\s*(.+)$")
FIELDS = ("요약", "역할", "주의", "개요", "흐름")


def parse_tagged(text: str) -> Tuple[Dict[str, str], Dict[int, str]]:
    fields: Dict[str, str] = {}
    notes: Dict[int, str] = {}
    cur: Any = None
    for ln in text.splitlines():
        if not ln.strip():
            continue
        m = FIELD_RE.match(ln)
        if m:
            cur = m.group(1)
            fields.setdefault(cur, m.group(2).strip())
            continue
        m = LINE_RE.match(ln)
        if m:
            n = int(m.group(1))
            notes.setdefault(n, m.group(2).strip())
            cur = ("L", n)
            continue
        if cur in FIELDS:
            fields[cur] = (fields[cur] + " " + ln.strip()).strip()
        elif isinstance(cur, tuple):
            notes[cur[1]] = (notes[cur[1]] + " " + ln.strip()).strip()
    return fields, notes


def hangul_ok(s: str, min_hangul: int = 3, ratio: float = 0.2) -> bool:
    h = len(re.findall(r"[가-힣]", s))
    l = len(re.findall(r"[A-Za-z]", s))
    return h >= min_hangul and h / max(1, h + l) >= ratio


def degenerate(s: str) -> bool:
    w = s.split()
    return len(w) >= 12 and len(set(w)) / len(w) < 0.35


BAD_PHRASES = ("as an ai", "i cannot", "i'm sorry", "죄송", "도와드릴 수 없", "알 수 없습니다만", "[함수]", "[코드]", "[출력 형식]")


def ground(text: str, known: set) -> Tuple[str, int, int]:
    """`백틱` 안의 식별자가 실제 코드에 존재하는지 검사. 없으면 백틱을 벗겨 '확정 표현'처럼 보이지 않게 함."""
    total = bad = 0

    def repl(m: "re.Match[str]") -> str:
        nonlocal total, bad
        inner = m.group(1)
        toks = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", inner)
        if not toks:
            return m.group(0)
        total += 1
        if any(t not in known for t in toks):
            bad += 1
            return inner
        return m.group(0)
    out = re.sub(r"`([^`\n]{1,60})`", repl, text)
    return out, total, bad


class Validator:
    def __init__(self, proj: "Project"):
        self.proj = proj
        self.global_known = set(BUILTINS) | set(keyword.kwlist) | set(proj.by_short.keys())
        for fr in proj.files:
            self.global_known.update(fr.module.split("."))
            self.global_known.update(Path(fr.rel).stem.split("."))

    def known_for(self, u: Unit) -> set:
        fr = self.proj.files[u.file]
        src = "\n".join(fr.lines[u.line - 1:u.end])
        k = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", src)) | self.global_known
        k.update(u.vars.keys())
        for e in u.callees:
            k.add(self.proj.units[e].name)
        return k

    def field(self, text: str, known: set, limit: int, need_hangul: bool = True) -> Tuple[Optional[str], int]:
        """returns (cleaned_text | None(reject), flags)"""
        t = " ".join((text or "").split())
        if not t or t in ("없음", "-", "없다", "없음."):
            return None, 0
        low = t.lower()
        if any(b in low for b in BAD_PHRASES) or degenerate(t):
            return None, 1
        if need_hangul and not hangul_ok(t):
            return None, 1
        t, total, bad = ground(t, known)
        flags = bad
        if bad >= 2 and bad * 2 >= total:
            return None, bad
        return clamp_sentences(t, limit), flags

    def func(self, u: Unit, text: str) -> Optional[dict]:
        fields, notes = parse_tagged(clean_llm_text(text))
        known = self.known_for(u)
        fr = self.proj.files[u.file]
        flags = 0
        out: Dict[str, Any] = {}
        s, f = self.field(fields.get("요약", ""), known, 120)
        flags += f
        if not s or s.replace("`", "") in (u.name, u.disp):
            return None
        out["s"] = s
        r, f = self.field(fields.get("역할", ""), known, 280)
        flags += f if r is not None or fields.get("역할") else 0
        if r:
            out["r"] = r
        c, f = self.field(fields.get("주의", ""), known, 200)
        if c:
            out["c"] = c
        lines: Dict[int, str] = {}
        dropped = 0
        for n, t in sorted(notes.items()):
            if not (u.line <= n <= u.end):
                dropped += 1
                continue
            info = fr.info.get(n)
            if info and info.get("k") == "cont":
                n = info.get("a", n)
                info = fr.info.get(n)
            if not info or info.get("k") in ("blank", "comment", "docstring"):
                dropped += 1
                continue
            lk = known | set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", fr.lines[n - 1]))
            nt, f = self.field(t, lk, 150)
            if not nt or n in lines:
                dropped += 1
                continue
            flags += f
            lines[n] = nt
            if len(lines) >= 8:
                break
        out["l"] = lines
        out["fl"] = flags + dropped
        out["st"] = "ok" if (flags + dropped) == 0 else "partial"
        return out

    def overview(self, text: str, known: set) -> Optional[dict]:
        fields, _ = parse_tagged(clean_llm_text(text))
        ov, f1 = self.field(fields.get("개요", ""), known, 420)
        if not ov:
            return None
        fl, f2 = self.field(fields.get("흐름", ""), known, 220, need_hangul=False)
        out = {"s": ov, "st": "ok" if (f1 + f2) == 0 else "partial"}
        if fl:
            out["f"] = fl
        return out


SYSTEM_PROMPT = (
    "너는 파이썬 코드 설명 도우미다. 반드시 지정된 형식의 한국어 텍스트만 출력한다. "
    "JSON, 마크다운 제목, 코드블록, 생각 과정, LaTeX 수식 기호($\\rightarrow$ 등)는 절대 쓰지 말고 유니코드 화살표(→)만 쓴다. "
    "주어진 코드와 '분석기가 확인한 사실'에 없는 내용은 절대 지어내지 않는다. 모르면 '없음'이라고 쓴다."
)
FEWSHOT = (
    "[예시 — 형식만 참고]\n"
    "요약: 점수 목록에서 평균을 구해 반환한다.\n"
    "역할: 보고서 출력 직전에 평균을 계산하는 보조 함수이다.\n"
    "주의: 빈 리스트를 넣으면 0 으로 나누기 오류가 난다.\n"
    "L3: 모든 점수를 더해 total 에 저장한다.\n"
    "L4: total 을 개수로 나눠 평균을 돌려준다.\n"
)


def build_func_prompt(proj: "Project", u: Unit, strict: bool = False) -> str:
    fr = proj.files[u.file]
    n_lines = u.end - u.line + 1
    full = n_lines <= 70
    sig = unit_signature(u)
    lines_out = ["[함수] " + u.disp + f"  (파일 {fr.rel}:{u.line}-{u.end})", "[시그니처] " + sig]
    if u.doc:
        lines_out.append("[독스트링] " + short(u.doc.replace("\n", " "), 200))
    lines_out.append("[분석기가 확인한 사실]")
    for b in u.static.get("bul", [])[:7]:
        lines_out.append("- " + b.replace("`", ""))
    if full:
        lines_out.append("[코드]")
        for ln in range(u.line, u.end + 1):
            lines_out.append(f"{ln}: {fr.lines[ln - 1]}")
    else:
        lines_out.append(f"[코드 구조 — 함수가 길어({n_lines}줄) 핵심 줄만 제공]")
        for it in u.outline[:60]:
            lines_out.append(f"{it['l']}: {it['t']}")
    lines_out.append("")
    lines_out.append(FEWSHOT)
    lines_out.append("[지금 출력할 형식]")
    lines_out.append("요약: (이 함수가 하는 일 한 문장, 60자 이내)")
    lines_out.append("역할: (프로그램에서 이 함수의 역할 1~2문장)")
    lines_out.append("주의: (초보자가 헷갈릴 점 한 문장, 없으면 없음)")
    if full:
        lines_out.append("L<줄번호>: (그 줄이 하는 일 한 문장)   ← 중요한 줄만 최대 6개, 위 [코드]의 줄번호만 사용")
    if strict:
        lines_out.append("※ 위 형식의 줄만 출력하라. 다른 문장·번호 목록·설명은 쓰지 마라.")
    return "\n".join(lines_out)


def unit_signature(u: Unit) -> str:
    if u.sig_str:
        return u.sig_str
    if u.kind != "function":
        return u.name
    ps = []
    for p in u.params:
        s = {"var": "*", "kwvar": "**"}.get(p["kind"], "") + p["name"]
        if p["ann"]:
            s += f": {p['ann']}"
        if p["default"] is not None:
            s += f" = {p['default']}"
        ps.append(s)
    pre = "async def" if isinstance(u.node, ast.AsyncFunctionDef) else "def"
    return f"{pre} {u.name}({', '.join(ps)})" + (f" -> {u.ret_ann}" if u.ret_ann else "")


class LLMCache:
    def __init__(self, path: Path):
        self.path = path
        self.lock = threading.Lock()
        self.data: Dict[str, Any] = {}
        try:
            if path.is_file():
                d = json.loads(path.read_text(encoding="utf-8"))
                if isinstance(d, dict):
                    self.data = d
        except Exception:
            self.data = {}

    def get(self, key: str) -> Any:
        return self.data.get(key)

    def put(self, key: str, val: Any) -> None:
        with self.lock:
            self.data[key] = val
            try:
                self.path.parent.mkdir(parents=True, exist_ok=True)
                tmp = self.path.with_suffix(".tmp")
                tmp.write_text(json.dumps(self.data, ensure_ascii=False), encoding="utf-8")
                os.replace(tmp, self.path)
            except OSError:
                pass


def static_overview(proj: "Project") -> dict:
    nfile = len(proj.files)
    nlines = sum(len(f.lines) for f in proj.files)
    funcs = [u for u in proj.units if u.kind == "function"]
    classes = [u for u in proj.units if u.kind == "class"]
    ents = sorted([u for u in proj.units if u.is_entry and u.kind == "function"],
                  key=lambda u: (0 if u.name == "main" else 1, -len(u.callees)))[:4]
    mod_ents = [u for u in proj.units if u.kind == "module" and u.callees][:3]
    top_called = sorted(funcs, key=lambda u: -len(u.callers))[:3]
    top_cplx = sorted(funcs, key=lambda u: -u.metrics.get("cc", 0))[:3]
    parts = [f"{nfile}개 파일(총 {nlines:,}줄), 클래스 {len(classes)}개, 함수·메서드 {len(funcs)}개로 구성된 프로젝트입니다."]
    if ents or mod_ents:
        names = [f"`{u.disp}`" for u in ents] + [f"`{u.disp}` 모듈 실행부" for u in mod_ents]
        parts.append("실행 흐름의 시작점 후보: " + ", ".join(names) + ".")
    if top_called and top_called[0].callers:
        parts.append("가장 많이 호출되는 함수: " + ", ".join(f"`{u.disp}`({len(u.callers)}곳)" for u in top_called if u.callers) + ".")
    if top_cplx:
        parts.append("가장 복잡한 함수: " + ", ".join(f"`{u.disp}`(복잡도 {u.metrics['cc']})" for u in top_cplx) + ".")
    libs = [k for k, _ in proj.ext_libs.most_common(6)]
    if libs:
        parts.append("주로 사용하는 외부 라이브러리: " + ", ".join(libs) + ".")
    flow = ""
    down = [proj.units[i] for i in proj.order.get("down", [])][:7]
    if down:
        flow = " → ".join((f"`{u.disp}`(모듈 실행부)" if u.kind == "module" else f"`{u.disp}`") for u in down)
    return {"s": "\n".join(parts), "f": flow}


class AIEnricher:
    def __init__(self, proj: "Project", client: LLMClient, cache: LLMCache, workers: int = 2,
                 max_calls: int = 150, log: Callable[[str], None] = print,
                 progress: Optional[Callable[[str, int, int], None]] = None):
        self.proj = proj
        self.client = client
        self.cache = cache
        self.workers = max(1, workers)
        self.max_calls = max_calls
        self.log = log
        self.progress = progress
        self.val = Validator(proj)
        self.lock = threading.Lock()
        self.stop = False
        self.transport_fail = 0
        self.reject_streak = 0
        self.stats = {"enabled": False, "model": client.model, "targets": 0, "ok": 0, "partial": 0,
                      "rejected": 0, "failed": 0, "cached": 0, "stopped": ""}
        self.overview: Optional[dict] = None

    def select(self) -> List[Unit]:
        cands = []
        for u in self.proj.units:
            if u.kind != "function":
                continue
            m = u.metrics
            if m["code"] < 5 and m["cc"] <= 1 and not u.callees:
                continue
            score = len(u.callers) * 2 + m["cc"] + m["code"] / 12 + (8 if u.is_entry else 0)
            cands.append((score, u))
        cands.sort(key=lambda x: -x[0])
        return [u for _, u in cands[: self.max_calls]]

    def one(self, u: Unit) -> None:
        if self.stop:
            return
        proj = self.proj
        prompt = build_func_prompt(proj, u)
        key = sha1(PROMPT_VERSION + "|" + self.client.model + "|" + prompt)
        cached = self.cache.get(key)
        if cached:
            u.ai = cached
            with self.lock:
                self.stats["cached"] += 1
            return
        result = None
        last_err = ""
        for attempt in range(2):
            if self.stop:
                return
            pr = prompt if attempt == 0 else build_func_prompt(proj, u, strict=True)
            try:
                txt, finish = self.client.complete(SYSTEM_PROMPT, pr, max_tokens=700)
            except LLMError as e:
                last_err = str(e)
                if e.transport:
                    with self.lock:
                        self.transport_fail += 1
                        if self.transport_fail >= 4:
                            self.stop = True
                            self.stats["stopped"] = f"연속 연결 실패: {e}"
                    time.sleep(1.0)
                continue
            with self.lock:
                self.transport_fail = 0
            result = self.val.func(u, txt)
            if result is not None:
                if finish == "length":
                    result["fl"] = result.get("fl", 0) + 1
                    result["st"] = "partial"
                break
            last_err = "형식/검증 실패"
        with self.lock:
            if result is None:
                if last_err == "형식/검증 실패":
                    self.stats["rejected"] += 1
                    self.reject_streak += 1
                    if self.reject_streak >= 8:
                        self.stop = True
                        self.stats["stopped"] = "모델이 출력 형식을 8회 연속 지키지 못해 AI 해설을 중단했습니다 (정적 해설로 계속 사용)."
                else:
                    self.stats["failed"] += 1
                return
            self.reject_streak = 0
            self.stats["ok" if result["st"] == "ok" else "partial"] += 1
        result["m"] = self.client.model
        u.ai = result
        self.cache.put(key, result)

    def run(self) -> dict:
        log = self.log
        if not self.client.preflight(log):
            self.stats["stopped"] = "LLM 연결 실패 또는 모델명 없음"
            return self.stats
        self.stats["enabled"] = True
        self.stats["model"] = self.client.model
        targets = self.select()
        self.stats["targets"] = len(targets)
        log(f"[AI] 함수 {len(targets)}개를 병렬 {self.workers}개로 요약합니다 (검증 실패분은 정적 해설로 대체).")
        done = 0
        with ThreadPoolExecutor(max_workers=self.workers) as ex:
            futs = [ex.submit(self.one, u) for u in targets]
            for f in futs:
                try:
                    f.result()
                except Exception as e:  # 개별 실패 무시
                    self.stats["failed"] += 1
                    log(f"  [AI] 내부 오류 무시: {e}")
                done += 1
                if self.progress:
                    self.progress("AI 해설", done, len(targets))
                if done % 10 == 0 or done == len(targets):
                    s = self.stats
                    log(f"  [AI] {done}/{len(targets)} · 통과 {s['ok']} · 부분검증 {s['partial']} · 거부 {s['rejected']} · 실패 {s['failed']} · 캐시 {s['cached']}")
        if self.stats["stopped"]:
            log("  [AI] " + self.stats["stopped"])
        if not self.stop:
            self.make_overview()
        return self.stats

    def make_overview(self) -> None:
        proj = self.proj
        st = static_overview(proj)
        lines = ["[프로젝트] " + proj.root.name, "[분석기가 확인한 사실]", "- " + st["s"].replace("`", "")]
        if st["f"]:
            lines.append("- 추정 실행 흐름: " + st["f"].replace("`", ""))
        lines.append("[주요 함수 요약]")
        top = sorted([u for u in proj.units if u.kind == "function"],
                     key=lambda u: -(len(u.callers) * 2 + u.metrics["cc"] + (8 if u.is_entry else 0)))[:14]
        for u in top:
            one = (u.ai or {}).get("s") or u.static.get("one", "")
            lines.append(f"- {u.disp}: {short(one.replace('`', ''), 90)}")
        lines += ["", "[지금 출력할 형식]", "개요: (이 프로젝트가 무엇을 하는지 2~3문장)",
                  "흐름: (핵심 함수 이름만 화살표로 연결, 예: main → run → save)"]
        prompt = "\n".join(lines)
        key = sha1(PROMPT_VERSION + "|ov|" + self.client.model + "|" + prompt)
        known = set(self.val.global_known)
        for u in proj.units:
            known.update(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", u.disp))
        known.update(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", prompt))
        cached = self.cache.get(key)
        if cached:
            self.overview = cached
            return
        for attempt in range(2):
            try:
                txt, _ = self.client.complete(SYSTEM_PROMPT, prompt, max_tokens=500)
            except LLMError:
                return
            ov = self.val.overview(txt, known)
            if ov:
                ov["m"] = self.client.model
                self.overview = ov
                self.cache.put(key, ov)
                return


# ═════════════════════════════════════════════════════════════════════════════
#  내보내기 / HTML 생성 / 실행기 / GUI
# ═════════════════════════════════════════════════════════════════════════════
def export_unit(proj: Project, u: Unit) -> dict:
    d: Dict[str, Any] = {
        "id": u.id, "k": u.kind[0], "n": u.name, "dn": u.disp, "f": u.file, "l": u.line, "e": u.end,
        "p": u.parent.id if u.parent else -1, "cl": u.cls.id if u.cls else -1,
        "sig": unit_signature(u), "doc": short(u.doc.replace("\n", " "), 320) if u.doc else "",
        "m": u.metrics, "st": u.static, "en": u.is_entry, "dd": u.is_dead, "rc": u.is_recursive,
        "cy": bool(getattr(u, "in_cycle", False)),
    }
    if u.kind != "class":
        d["pa"] = [{"n": p["name"], "t": p["ann"], "d": p["default"], "k": p["kind"]} for p in u.params]
        d["ret"] = u.ret_ann
        d["rets"] = u.rets[:4]
        d["ef"] = sorted(u.effects)
        d["co"] = [[t, e["k"], e["lines"]] for t, e in u.callees.items()]
        d["va"] = [[v["name"], v["kind"], v["type"], v["defs"], v["uses"]] for v in u.vars.values()]
        d["ex"] = [[k, v["kind"], v.get("id", v.get("canon", "")), v["line"]] for k, v in list(u.externals.items())[:40]]
        d["ol"] = u.outline
        d["xc"] = [[c, n, KB_CALLS.get(c) or KB_FOREIGN.get(c, "")] for c, n in u.ext_calls.most_common(12)]
        d["stps"] = u.steps
    d["ca"] = [[t, e["k"], e["lines"]] for t, e in u.callers.items()]
    if u.kind == "class":
        d["at"] = [[k, v["type"], v["where"], v["line"]] for k, v in u.attrs.items()]
        d["ch"] = [c.id for c in u.children if c.kind == "function"]
        d["bs"] = [b.id for b in proj.class_bases.get(u.id, [])]
    if u.decos:
        d["dc"] = u.decos
    if u.ai:
        d["ai"] = u.ai
    return d


def export_all(proj: Project, ai_stats: dict, ai_overview: Optional[dict], title: str) -> Tuple[dict, List[dict]]:
    dependents: Dict[int, List[int]] = defaultdict(list)
    for fr in proj.files:
        for d in fr.deps:
            dependents[d].append(fr.idx)
    files = []
    fdata = []
    for fr in proj.files:
        files.append({
            "id": fr.idx, "path": fr.rel, "mod": fr.module, "lang": fr.lang, "n": len(fr.lines), "err": fr.err,
            "deps": sorted(fr.deps), "by": sorted(dependents.get(fr.idx, [])),
            "mu": fr.module_unit.id if fr.module_unit else -1,
            "us": [u.id for u in proj.units if u.file == fr.idx],
        })
        infos = []
        for ln in range(1, len(fr.lines) + 1):
            infos.append(fr.info.get(ln) or {"k": "blank"})
        fdata.append({"L": proj.build_segments(fr), "I": infos})
    funcs = [u for u in proj.units if u.kind == "function"]
    stats = {
        "files": len(proj.files), "lines": sum(len(f.lines) for f in proj.files),
        "classes": len([u for u in proj.units if u.kind == "class"]), "funcs": len(funcs),
        "edges": sum(len(u.callees) for u in proj.units),
        "libs": [[k, v] for k, v in proj.ext_libs.most_common(10)],
    }
    data = {
        "title": title, "ver": VERSION, "gen": time.strftime("%Y-%m-%d %H:%M"),
        "stats": stats, "files": files, "units": [export_unit(proj, u) for u in proj.units],
        "order": proj.order, "so": static_overview(proj),
        "ai": {"stats": ai_stats, "ov": ai_overview},
        "errors": proj.errors[:20],
    }
    return data, fdata


_EMBEDDED_TEMPLATE = r"""<!DOCTYPE html>
<html lang="ko">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>__TITLE__ — Code Tutor</title>
<style>
:root{--fs:13.5px;--fs-l:13.5px;--fs-c:13.5px;--fs-r:13.5px;--bg:#0e1420;--bg2:#141c2b;--bg3:#1a2437;--hdr1:#1e2940;--hdr2:#151d2e;--hdrbd:#3c5885;--panehdr:#2a231c;--panehdrbd:#6e5a41;--sub:#101725;--code:#0b101a;--bd:#27344b;--tx:#e6edf7;--mu:#8b9bb4;--ac:#4cc2ff;--acbg:#4cc2ff22;--ok:#3ddc97;--warn:#ffb454;--bad:#ff6b6b;--kw:#c792ea;--st:#8bd87a;--nu:#f6a560;--cm:#6b7a94;--fn:#6cb6ff;--bi:#7fd1d1;--vh:#ffd86633}
:root.light{--bg:#f6f8fb;--bg2:#ffffff;--bg3:#eef2f8;--hdr1:#dfe8f6;--hdr2:#e9eff8;--hdrbd:#8db0db;--panehdr:#f3ece1;--panehdrbd:#c8b69c;--sub:#eaf0f8;--code:#ffffff;--bd:#d5dde9;--tx:#1b2433;--mu:#5c6b82;--ac:#0b73c9;--acbg:#0b73c91a;--ok:#12805a;--warn:#a96100;--bad:#c4372f;--kw:#8a3fc2;--st:#2f7d1f;--nu:#b85a10;--cm:#7d8aa0;--fn:#1558b0;--bi:#12767a;--vh:#ffd86655}
*{box-sizing:border-box}
html,body{height:100%;margin:0}
body{background:var(--bg);color:var(--tx);font:var(--fs)/1.55 -apple-system,BlinkMacSystemFont,"Malgun Gothic","Apple SD Gothic Neo","Segoe UI",sans-serif;overflow:hidden}
button{font:inherit;color:inherit;background:var(--bg3);border:1px solid var(--bd);border-radius:6px;padding:3px 9px;cursor:pointer}
button:hover{border-color:var(--ac)}
button:disabled{opacity:.42;cursor:not-allowed}
button:disabled:hover{border-color:var(--bd)}
button.on{background:var(--acbg);border-color:var(--ac);color:var(--ac)}
#bAi.on{background:#3ddc9722;border-color:var(--ok);color:var(--ok);font-weight:700}
input,select{font:inherit;color:var(--tx);background:var(--bg);border:1px solid var(--bd);border-radius:6px;padding:4px 8px}
code,.mono{font-family:"D2Coding","Cascadia Mono",Consolas,Menlo,monospace}
code{background:var(--bg3);border-radius:4px;padding:0 4px;font-size:.92em;color:var(--warn)}
#app{height:100vh;display:flex;flex-direction:column}
.pane-hdr{height:42px;display:flex;align-items:center;gap:6px;padding:0 10px;background:var(--panehdr);border-bottom:1.5px solid var(--panehdrbd);box-shadow:inset 0 2px 0 #9a7846aa;flex-shrink:0;font-size:13px}
:root.light .pane-hdr{box-shadow:inset 0 2px 0 #c4955266}
.pane-hdr .sp{flex:1}
.ghost-btn{border:1px solid transparent;background:transparent;color:var(--mu);padding:4px 7px;border-radius:7px;line-height:1;transition:background .15s,color .15s,border-color .15s}
.ghost-btn:hover{background:var(--bg3);color:var(--tx);border-color:var(--bd)}
.ghost-btn.on{background:var(--acbg);border-color:var(--ac);color:var(--ac)}
.pane-proj{display:inline-flex;align-items:center;gap:6px;background:var(--bg2);border:1px solid var(--bd);border-radius:8px;padding:4px 10px;font-weight:600;color:var(--tx);white-space:nowrap;transition:border-color .15s,background .15s}
.pane-proj:hover{border-color:var(--ac);background:var(--bg3)}
.pane-search{display:inline-flex;align-items:center;gap:5px;background:var(--bg);border:1px solid var(--bd);border-radius:8px;padding:4px 9px;color:var(--mu);font-size:.9em;white-space:nowrap;transition:border-color .15s,color .15s}
.pane-search:hover{border-color:var(--ac);color:var(--tx)}
.pane-search kbd{font-family:inherit;font-size:.82em;padding:1px 5px;border-radius:4px;background:var(--bg3);border:1px solid var(--bd);color:var(--mu)}
#bLlmCfg,#bAi{padding:3px 7px;font-size:.88em;border-radius:7px;white-space:nowrap;flex-shrink:0}
#lcWrap{flex:1;min-width:0;display:flex;flex-direction:column}
#lcBody{flex:1;min-height:0;display:flex}
#footBar{flex-shrink:0;display:flex;align-items:center;gap:8px;padding:4px 12px;background:var(--panehdr);border-top:1.5px solid var(--panehdrbd);box-shadow:inset 0 2px 0 #9a7846aa;font-size:.86em;min-height:30px}
:root.light #footBar{box-shadow:inset 0 2px 0 #c4955266}
#footBar .add-logo{display:inline-flex;align-items:center;background:#ffffff;padding:2px 6px;border-radius:5px;border:1px solid #0002;flex-shrink:0}
#footBar .add-logo img{height:18px;width:auto;display:block}
#footBar .brand{font-weight:800;color:var(--ac);white-space:nowrap;letter-spacing:.2px;flex-shrink:0}
#footBar .sep{color:var(--bd);user-select:none;flex-shrink:0}
#footBar .ttl{color:var(--tx);opacity:.85;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;min-width:0}
#footBar .sp{flex:1}
#footBar > button{padding:2px 8px;flex-shrink:0}
#footBar .fgrp{flex-shrink:0}
.tabs{display:flex;gap:2px;background:var(--bg);padding:3px;border-radius:8px;border:1px solid var(--bd);flex-shrink:0}
.tabs button{border:0;border-radius:6px;background:transparent;color:var(--mu);padding:3px 10px;font-size:.92em;font-weight:500;white-space:nowrap;transition:background .15s,color .15s}
.tabs button:hover{color:var(--tx);background:var(--bg3)}
.tabs button.on{background:var(--ac);color:#04121f;font-weight:700;box-shadow:0 1px 4px #0004}
:root.light .tabs button.on{color:#ffffff}
.sp{flex:1}
#main{flex:1;display:flex;min-height:0}
#side{width:var(--sw,300px);background:var(--bg2);border-right:1px solid var(--bd);display:flex;flex-direction:column;min-width:180px;font-size:var(--fs-l);overflow:hidden;transition:width .22s ease,min-width .22s ease,opacity .18s ease}
#tutor{width:var(--tw,480px);background:var(--bg2);border-left:1px solid var(--bd);display:flex;flex-direction:column;min-width:260px;font-size:var(--fs-r);overflow:hidden;transition:width .22s ease,min-width .22s ease,opacity .18s ease}
#side.col,#tutor.col{width:0 !important;min-width:0 !important;opacity:0;border-width:0;pointer-events:none}
body.resizing #side,body.resizing #tutor{transition:none}
#center{flex:1;min-width:0;display:flex;flex-direction:column;position:relative;font-size:var(--fs-c)}
.split{width:7px;cursor:col-resize;background:var(--bg);flex-shrink:0;position:relative;display:flex;align-items:center;justify-content:center;overflow:visible;z-index:10}
.split:hover,.split.drag{background:var(--acbg)}
.spbtn{position:relative;z-index:2;width:15px;height:42px;padding:0;font-size:11px;line-height:1;border-radius:5px;background:var(--hdr1);border:1px solid var(--hdrbd);color:var(--tx);display:flex;align-items:center;justify-content:center;cursor:pointer;flex-shrink:0;box-shadow:0 2px 6px #0004}
.spbtn:hover{background:var(--ac);color:#04121f;border-color:var(--ac)}
.tuttabs{display:flex;gap:2px;background:var(--bg);padding:3px;border-radius:8px;border:1px solid var(--bd);flex-shrink:0;min-width:0}
.tuttabs button{border:0;border-radius:6px;background:transparent;color:var(--mu);padding:3px 7px;font-size:.88em;font-weight:500;white-space:nowrap;transition:background .15s,color .15s}
.tuttabs button:hover{color:var(--tx);background:var(--bg3)}
.tuttabs button.on{background:var(--ac);color:#04121f;font-weight:700;box-shadow:0 1px 4px #0004}
:root.light .tuttabs button.on{color:#ffffff}
.sidetabs{display:flex;gap:4px;padding:6px 8px;background:var(--sub);border-bottom:1.5px solid var(--hdrbd);flex-shrink:0}
.sidetabs button{flex:1;border:1px solid var(--bd);border-radius:7px;background:var(--bg2);color:var(--mu);padding:5px 4px;font-size:.86em;font-weight:500;transition:border-color .15s,background .15s,color .15s}
.sidetabs button:hover{color:var(--tx);background:var(--bg3);border-color:var(--hdrbd)}
.sidetabs button.on{color:var(--ac);border:1.5px solid var(--ac);background:var(--acbg);font-weight:700;box-shadow:0 1px 4px #0003}
.sbsearch{position:relative;padding:7px 8px;background:var(--bg);border-bottom:1.5px solid var(--hdrbd);flex-shrink:0}
.sbsearch .sbico{position:absolute;left:17px;top:50%;transform:translateY(-50%);color:var(--mu);font-size:.88em;pointer-events:none}
.sbsearch input{width:100%;background:var(--code);border:1.5px solid var(--hdrbd);border-radius:8px;padding:6px 10px 6px 28px;color:var(--tx);box-shadow:inset 0 1px 3px #0003;transition:border-color .15s,box-shadow .15s}
.sbsearch input:hover{border-color:var(--ac)}
.sbsearch input:focus{outline:none;border-color:var(--ac);box-shadow:0 0 0 2px var(--acbg)}
.scroll{overflow:auto;flex:1;min-height:0}
.pad{padding:10px 12px}
.row{display:flex;align-items:center;gap:6px;padding:2px 8px;cursor:pointer;border-radius:5px;white-space:nowrap;overflow:hidden}
.row:hover{background:var(--bg3)}
.row.act{background:var(--acbg);color:var(--ac)}
.row .nm{overflow:hidden;text-overflow:ellipsis;flex:1}
.row .mt{color:var(--mu);font-size:.8em}
.dir{color:var(--mu);font-size:.8em;padding:8px 8px 2px;text-transform:none}
.dot{display:inline-block;width:8px;height:8px;border-radius:50%;flex-shrink:0}
.d1{background:#3ddc97}.d2{background:#9be15d}.d3{background:#ffd166}.d4{background:#ff9f45}.d5{background:#ff5d5d}
.tag{font-size:.74em;padding:0 6px;border-radius:999px;border:1px solid var(--bd);color:var(--mu);white-space:nowrap}
.tag.ent{color:var(--ok);border-color:var(--ok)}.tag.dead{color:var(--warn);border-color:var(--warn)}.tag.rec{color:var(--kw);border-color:var(--kw)}
.badge{font-size:.72em;padding:1px 7px;border-radius:999px;font-weight:600;white-space:nowrap}
.b-st{background:#3ddc9722;color:var(--ok);border:1px solid #3ddc9755}
.b-ai{background:#ffb45422;color:var(--warn);border:1px solid #ffb45466}
.b-ai.ok{background:#4cc2ff22;color:var(--ac);border-color:#4cc2ff66}
#codewrap{flex:1;display:flex;flex-direction:column;min-height:0}
.crumb{display:flex;align-items:center;gap:8px;padding:5px 12px;background:var(--sub);border-bottom:1px solid var(--bd);flex-shrink:0;flex-wrap:wrap}
.crumb a{color:var(--ac);cursor:pointer}.crumb a:hover{text-decoration:underline}
#code{flex:1;overflow:auto;background:var(--code);padding:6px 0;font-family:"D2Coding","Cascadia Mono",Consolas,Menlo,monospace;font-size:calc(var(--fs-c) - 0.5px);line-height:1.6}
.ln{display:flex;border-left:3px solid transparent;cursor:pointer;min-width:max-content;content-visibility:auto;contain-intrinsic-size:auto 22px}
.ln:hover{background:var(--bg3)}
.ln.stm{background:var(--acbg)}
.ln.sel-block{background:#ffd8661f;border-left-color:var(--warn)}
.ln.act{background:#4cc2ff2e;border-left-color:var(--ac)}
.ln.hid{display:none}
.ln .gt{width:52px;text-align:center;color:var(--mu);flex-shrink:0;user-select:none;font-size:11px;display:flex;align-items:center;justify-content:center;gap:3px}
.sbadge{display:inline-block;padding:0 4px;border-radius:4px;font-size:10px;line-height:15px;background:var(--acbg);color:var(--ac);border:1px solid #4cc2ff55;cursor:pointer;font-weight:700}
.sbadge:hover,.sbadge.on{background:var(--ac);color:#04121f}
.ln .nm{width:44px;text-align:right;padding-right:12px;color:var(--cm);flex-shrink:0;user-select:none}
.ln.act .nm{color:var(--ac);font-weight:700}
.ln .tx{white-space:pre;tab-size:4;padding-right:24px}
.fold{cursor:pointer;color:var(--mu)}.fold:hover{color:var(--ac)}
.aid{color:var(--warn)}
.kw{color:var(--kw);font-weight:600}.str{color:var(--st)}.num{color:var(--nu)}.cmt{color:var(--cm);font-style:italic}.bi{color:var(--bi)}.df{color:var(--fn);font-weight:700}.cl{color:var(--warn);font-weight:700}.dec{color:var(--warn)}.slf{color:var(--mu);font-style:italic}
.call{color:var(--fn);text-decoration:underline dotted;text-underline-offset:3px}
.call.g{text-decoration-style:dashed;opacity:.85}
.ref{color:var(--fn);text-decoration:underline wavy;text-underline-offset:3px}
.ext{color:var(--fn)}
[data-v]{cursor:pointer}
[data-v]:hover{background:var(--vh)}
.vh{background:var(--vh);border-radius:3px;outline:1px solid #ffd86688}
.card{background:var(--bg3);border:1px solid var(--bd);border-radius:10px;padding:10px 12px;margin-bottom:10px}
.card h4{margin:0 0 6px;font-size:.92em;color:var(--ac);display:flex;align-items:center;gap:8px}
.card h4 .sp{flex:1}
.muted{color:var(--mu)}
.small{font-size:.86em}
.chip{display:inline-block;margin:2px 4px 2px 0;padding:1px 8px;border:1px solid var(--bd);border-radius:6px;background:var(--bg);cursor:pointer;font-family:"D2Coding",Consolas,monospace;font-size:.88em;max-width:100%;overflow:hidden;text-overflow:ellipsis;vertical-align:bottom;white-space:nowrap}
.chip:hover{border-color:var(--ac)}
.chip.v{color:var(--warn)}.chip.w{color:var(--ok)}.chip.m{color:var(--bad)}.chip.g{opacity:.75;border-style:dashed}
.chip.on{background:var(--vh);border-color:var(--warn)}
table{width:100%;border-collapse:collapse;font-size:.88em}
th,td{text-align:left;padding:3px 6px;border-bottom:1px solid var(--bd);vertical-align:top}
th{color:var(--mu);font-weight:500}
tr.hl td{background:var(--acbg)}
tr.cl{cursor:pointer}tr.cl:hover td{background:var(--bg)}
.grid{display:grid;grid-template-columns:repeat(4,1fr);gap:6px}
.kpi{background:var(--bg);border:1px solid var(--bd);border-radius:8px;padding:6px 10px;display:flex;align-items:baseline;justify-content:center;gap:6px;white-space:nowrap}
.kpi b{font-size:1.12em}
.kpi span{font-size:.86em;color:var(--mu)}
.bar{height:6px;border-radius:3px;background:var(--bd);overflow:hidden}.bar i{display:block;height:100%}
.ol{font-family:"D2Coding",Consolas,monospace;font-size:.86em}
.ol div{cursor:pointer;padding:1px 4px;border-radius:4px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ol div:hover{background:var(--bg)}
.ol .k-if,.ol .k-elif,.ol .k-else{color:var(--kw)}.ol .k-for,.ol .k-while{color:var(--bi)}.ol .k-return{color:var(--ok)}.ol .k-raise,.ol .k-except{color:var(--bad)}.ol .k-try,.ol .k-finally{color:var(--warn)}
.sec{padding:14px 18px;overflow:auto;flex:1}
.sec h2{font-size:1.05em;margin:16px 0 8px;color:var(--ac)}
.sec h2:first-child{margin-top:0}
.gtool{display:flex;flex-direction:column;background:var(--bg2);border-bottom:1px solid var(--bd);flex-shrink:0}
.gtool-row{display:flex;gap:4px;align-items:center;padding:5px 8px;flex-wrap:wrap}
.gtool-row+.gtool-row{border-top:1px solid var(--bd);background:var(--sub);padding:5px 8px}
.gtool-row .sp{flex:1}
.gctrl{display:inline-flex;align-items:center;gap:4px;background:var(--code);border:1px solid var(--hdrbd);border-radius:8px;padding:2px 4px 2px 6px;box-shadow:0 1px 3px #0002;transition:border-color .15s,box-shadow .15s}
.gctrl:hover,.gctrl:focus-within{border-color:var(--ac);box-shadow:0 0 0 1px var(--acbg)}
.gctrl>span{font-size:.78em;font-weight:600;color:var(--mu);white-space:nowrap}
.gctrl select{background:var(--bg3);color:var(--tx);border:1px solid var(--bd);border-radius:6px;padding:2px 4px;font-size:.83em;font-weight:600;cursor:pointer}
.gctrl select:focus{outline:none;border-color:var(--ac)}
.gchk{display:inline-flex;align-items:center;gap:5px;background:var(--code);border:1px solid var(--hdrbd);border-radius:8px;padding:3px 9px;font-size:.84em;font-weight:600;color:var(--tx);cursor:pointer;box-shadow:0 1px 3px #0002;transition:border-color .15s;white-space:nowrap}
.gchk:hover{border-color:var(--ac)}
.gchk input{margin:0;accent-color:var(--ac);cursor:pointer}
#gFit,#gPop,.gnav{background:var(--bg3);border:1px solid var(--hdrbd);border-radius:8px;padding:3px 7px;font-size:.82em;font-weight:600;box-shadow:0 1px 3px #0002;white-space:nowrap}
#gFit:hover,#gPop:hover,.gnav:hover:not(:disabled){border-color:var(--ac);color:var(--ac)}
.gnav{padding:3px 6px}
#gsvg,#fsvg{background:var(--code);cursor:grab;width:100%;height:100%;display:block}
#gsvg.pan{cursor:grabbing}
.gn rect{fill:var(--bg3);stroke:var(--bd);stroke-width:1}
.gn:hover rect{stroke:var(--ac)}
.gn.cur rect{stroke:var(--ac);stroke-width:2.5;fill:var(--acbg)}
.gn text{fill:var(--tx);font:12px "D2Coding",Consolas,monospace;pointer-events:none}
.gn text.s{fill:var(--mu);font-size:10px}
.ge{fill:none;stroke:var(--mu);stroke-width:1.3;opacity:.8}
.ge.ref{stroke-dasharray:5 3}.ge.guess{stroke-dasharray:1.5 3;opacity:.5}
.ge.hi{stroke:var(--ac);opacity:1;stroke-width:2}
#pal{position:fixed;inset:0;background:#0009;display:none;align-items:flex-start;justify-content:center;padding-top:12vh;z-index:50}
#pal.show{display:flex}
#pal .box{width:min(640px,92vw);background:var(--bg2);border:1px solid var(--bd);border-radius:12px;overflow:hidden}
#pal input{width:100%;border:0;border-bottom:1px solid var(--bd);border-radius:0;padding:12px 14px;font-size:1.05em}
#pal .res{max-height:50vh;overflow:auto}
#pal .res .row{padding:6px 14px}
#help,#llmModal,#projModal,#wikiModal,#ovGraphModal{position:fixed;inset:0;background:#0009;display:none;align-items:center;justify-content:center;z-index:50}
#help.show,#llmModal.show,#projModal.show,#wikiModal.show,#ovGraphModal.show{display:flex}
#help .box,#llmModal .box,#projModal .box,#wikiModal .box,#ovGraphModal .box{background:var(--bg2);border:1px solid var(--bd);border-radius:12px;padding:16px 20px;width:min(540px,92vw)}
#wikiModal .box{width:min(760px,95vw);max-height:86vh;display:flex;flex-direction:column;gap:8px}
#wikiDocList{overflow:auto;max-height:28vh;display:flex;flex-direction:column;gap:5px}
.wdoc{display:flex;align-items:center;gap:8px;padding:7px 10px;border:1px solid var(--bd);border-radius:8px;background:var(--bg);cursor:pointer}
.wdoc:hover,.wdoc.on{border-color:var(--ac);background:var(--acbg)}
#wikiPreview{overflow:auto;max-height:28vh;border:1px solid var(--bd);border-radius:8px;padding:10px;background:var(--bg);font-size:.9em}
.wiki-refs{margin-top:10px;border-top:1px solid rgba(255,255,255,.26);padding-top:8px;font-size:.86em}
:root.light .wiki-refs{border-top-color:rgba(17,24,39,.22)}
.wiki-refs>summary{cursor:pointer;color:var(--ac);font-weight:600;user-select:none}
.wiki-ref-item{margin-top:6px;padding:6px 8px;border-radius:6px;background:var(--bg);border:1px solid var(--bd)}
.wiki-ref-hdr{display:flex;align-items:center;gap:6px;flex-wrap:wrap}
.wiki-ref-doc{color:var(--ac);font-weight:600;cursor:pointer;text-decoration:underline;text-underline-offset:2px}
.wiki-ref-doc:hover{opacity:.85}
.wiki-ref-body{margin-top:4px;line-height:1.58}
.wiki-ref-body details>summary{cursor:pointer;color:var(--mu);font-size:.9em;user-select:none}
#ovGraphModal .box{width:min(1240px,94vw);height:86vh;display:flex;flex-direction:column;gap:8px;padding:12px 16px}
#osvgPop{background:var(--code);width:100%;height:100%;display:block;border-radius:8px;cursor:grab}
#osvgPop.pan{cursor:grabbing}
#projModal .box{width:min(680px,94vw);max-height:84vh;display:flex;flex-direction:column}
#projList{margin-top:8px;overflow:auto;max-height:48vh;display:flex;flex-direction:column;gap:6px}
.pitem{display:flex;align-items:center;gap:8px;padding:8px 10px;border:1px solid var(--bd);border-radius:8px;background:var(--bg)}
.pitem.cur{border-color:var(--ac);background:var(--acbg)}
.pitem .pmain{flex:1;min-width:0}
.pitem .pnm{font-weight:700;display:flex;align-items:center;gap:6px;flex-wrap:wrap}
.pitem .proot{font-size:.82em;color:var(--mu);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
#llmModal .frow{display:flex;flex-direction:column;gap:3px;margin:8px 0}
#llmModal input[type=text],#llmModal input[type=password]{width:100%}
kbd{background:var(--bg3);border:1px solid var(--bd);border-bottom-width:2px;border-radius:5px;padding:0 6px;font-size:.85em;font-family:inherit}
#toast{position:fixed;bottom:18px;left:50%;transform:translateX(-50%);background:var(--ac);color:#04121f;padding:6px 14px;border-radius:8px;opacity:0;pointer-events:none;transition:opacity .2s;z-index:60;font-weight:600}
#toast.show{opacity:1}
.hint{border-left:3px solid var(--ac);padding:4px 10px;margin:10px 0;color:var(--mu);font-size:.92em;line-height:1.6}
.ov-sum{margin:4px 0 0;padding-left:18px;line-height:1.65}
.ov-sum li{margin:4px 0}
.ov-flow{border-top:1px solid #ffffff;padding-top:10px;margin-top:12px}
:root.light .ov-flow{border-top-color:#111827}
.cm{border-left:3px solid var(--cm);padding:2px 10px;margin:6px 0;color:var(--mu);font-style:italic}
.legend{display:inline-flex;gap:10px;align-items:center;flex-wrap:wrap;color:var(--tx);font-size:.84em;font-weight:500;background:var(--code);border:1px solid var(--bd);border-radius:8px;padding:3px 9px}
.legend-item{display:inline-flex;align-items:center;gap:5px;white-space:nowrap}
.legend svg{vertical-align:middle;flex-shrink:0}
#tutChatWrap{flex:1;display:flex;flex-direction:column;min-height:0}
#tutTop{flex-shrink:0;max-height:42%;overflow:auto;border-bottom:2px solid var(--hdrbd);padding:9px 11px;background:linear-gradient(180deg,var(--sub) 0%,var(--hdr2) 100%);box-shadow:0 3px 10px #0004}
.top-sum{margin-top:5px;padding:4px 8px;border:1px solid var(--bd);border-radius:7px;background:var(--bg);cursor:pointer;user-select:none;display:flex;align-items:flex-start;gap:6px}
.top-sum:hover{border-color:var(--ac)}
.top-sum.fold .top-sum-txt{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.top-box{margin-top:6px;padding:5px 8px;border:1px solid var(--bd);border-radius:7px;background:var(--bg)}
.top-box-lbl{font-size:.76em;font-weight:700;color:var(--mu);margin-bottom:4px;display:flex;align-items:center;gap:4px}
#tutThread{flex:1;min-height:0;overflow:auto;padding:10px}
#tutInput{flex-shrink:0;border-top:2px solid var(--hdrbd);padding:10px 12px;background:linear-gradient(180deg,var(--hdr2) 0%,var(--sub) 100%);box-shadow:0 -4px 14px #0005}
.chat-box{background:var(--code);border:1.5px solid var(--hdrbd);border-radius:16px;padding:8px 10px 7px 12px;display:flex;flex-direction:column;gap:5px;box-shadow:0 3px 12px #0004;transition:border-color .15s,box-shadow .15s}
.chat-box:focus-within{border-color:var(--ac);box-shadow:0 0 0 2px var(--acbg)}
#chatIn{width:100%;resize:none;font:inherit;color:var(--tx);background:transparent;border:0;padding:2px 0;min-height:40px;line-height:1.5;outline:none}
.chat-bar{display:flex;align-items:center;gap:6px;padding-top:4px;border-top:1px dashed var(--bd)}
#chatTarget{max-width:46%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex-shrink:1}
.chat-bar select,.chat-bar button:not(#bSendChat){font-size:.82em;padding:2px 8px;white-space:nowrap;flex-shrink:0}
#bSendChat{width:34px;height:34px;min-width:34px;padding:0;border-radius:50%;border:0;background:var(--ac);color:#04121f;display:inline-flex;align-items:center;justify-content:center;flex-shrink:0;box-shadow:0 2px 6px #0004;transition:transform .12s,filter .12s}
:root.light #bSendChat{color:#ffffff}
#bSendChat:hover{filter:brightness(1.1);transform:translateY(-1px)}
#bSendChat:active{transform:translateY(0)}
#bSendChat svg{width:18px;height:18px;display:block}
.step-pills{display:flex;flex-wrap:wrap;gap:4px;margin-top:6px}
.spill{font-size:.78em;padding:2px 8px;border-radius:999px;border:1px solid var(--bd);background:var(--bg);color:var(--mu);cursor:pointer}
.spill:hover{border-color:var(--ac);color:var(--tx)}
.spill.on{background:var(--acbg);border-color:var(--ac);color:var(--ac);font-weight:600}
.pin-item{background:var(--bg);border:1px solid #ffb45455;border-radius:7px;padding:6px 8px;margin-top:5px;font-size:.84em}
.pin-head{display:flex;align-items:center;gap:6px;color:var(--warn);font-weight:600;margin-bottom:2px}
.brief-card{border-color:#4cc2ff55}
.msg-user{background:var(--acbg);border:1px solid #4cc2ff55;border-radius:10px;padding:7px 10px;margin:8px 0 6px 20px;font-size:.92em}
.msg-asst{background:var(--bg3);border:1px solid var(--bd);border-radius:10px;padding:10px 12px;margin:0 0 10px}
.sugg-wrap{display:flex;flex-wrap:wrap;gap:5px;margin:6px 0 10px}
.sugg-btn{font-size:.8em;padding:4px 9px;border-radius:8px;background:var(--bg);border:1px solid var(--bd);color:var(--tx);cursor:pointer;text-align:left}
.sugg-btn:hover{border-color:var(--ac);background:var(--acbg);color:var(--ac)}
.msg-actions{display:flex;gap:6px;margin-top:8px;flex-wrap:wrap}
.msg-actions button{font-size:.78em;padding:2px 8px}
.md p{margin:10px 0}.md ul{margin:6px 0 12px;padding-left:18px}.md li{margin:9px 0}
.md .md-sec{margin:16px 0 6px;padding-top:10px;border-top:1px solid rgba(255,255,255,.22);font-weight:700;color:var(--ac)}
.md .md-sec:first-child{margin-top:4px;padding-top:0;border-top:0}
.md-tbl-wrap{margin:10px 0;overflow-x:auto;border:1px solid var(--bd);border-radius:8px}
.md table{width:100%;border-collapse:collapse;font-size:.9em}
.md th,.md td{padding:7px 10px;border-bottom:1px solid var(--bd);border-right:1px solid var(--bd);text-align:left;vertical-align:top}
.md th:last-child,.md td:last-child{border-right:0}
.md tr:last-child td{border-bottom:0}
.md th{background:var(--code);font-weight:700;color:var(--ac);white-space:nowrap}
.brief-sec{margin-top:12px;padding-top:10px;border-top:1px solid rgba(255,255,255,.24)}
.brief-sec:first-of-type{margin-top:6px;padding-top:0;border-top:0}
:root.light .md .md-sec,:root.light .brief-sec{border-top-color:rgba(17,24,39,.2)}
.var-card{border-color:#ffd86688;background:var(--bg2)}
.vt-sec{margin-top:11px;padding-top:8px;border-top:1px dashed var(--bd)}
.vt-sec:first-of-type{margin-top:6px;padding-top:0;border-top:0}
.vt-lbl{font-size:.83em;font-weight:700;color:var(--warn);margin-bottom:4px}
.vt-item{margin:5px 0}
.selpill{background:#ffb45422;border:1px solid #ffb45477;color:var(--warn);border-radius:999px;padding:1px 8px;font-size:.8em;display:inline-flex;align-items:center;gap:6px}
.utog{display:inline-block;width:14px;text-align:center;color:var(--mu);cursor:pointer;flex-shrink:0}.utog:hover{color:var(--ac)}
.treebar{display:flex;gap:4px;padding:5px 8px;border-bottom:1px solid var(--bd)}.treebar button{flex:1;font-size:.78em;padding:2px 6px}
.fgrp{display:inline-flex;align-items:center;gap:2px;background:var(--bg);border:1px solid var(--bd);border-radius:7px;padding:2px 3px}.fgrp button{padding:2px 6px;font-size:.86em;border:0;background:transparent}.fgrp button:hover{background:var(--bg3)}.fgrp select{border:0;background:var(--bg);color:var(--tx);padding:1px 4px;font-size:.84em;cursor:pointer}
select option{background:var(--bg2);color:var(--tx)}
#tip{position:fixed;display:none;pointer-events:none;z-index:95;background:var(--bg2);color:var(--tx);border:1px solid var(--ac);border-radius:7px;padding:5px 10px;font-size:.85em;line-height:1.4;max-width:480px;white-space:pre-wrap;word-break:break-word;box-shadow:0 6px 20px #0007}
.dir.cl{cursor:pointer}.dir.cl:hover{color:var(--tx)}
.tbtn{padding:1px 6px;font-size:.8em}
.tbtn.bmk{color:var(--warn);border-color:var(--warn);background:#ffb45422}
.tbtn.dn{color:var(--ok);border-color:var(--ok);background:#3ddc9722}
.card-tog{cursor:pointer;user-select:none}.card-tog:hover{opacity:.85}
.thread-bar{display:flex;align-items:center;gap:6px;margin-bottom:8px}
.thread-bar button{font-size:.78em;padding:2px 8px}
.msg-user.cl{cursor:pointer;user-select:none}.msg-user.cl:hover{border-color:var(--ac)}
.lang-tag{font-size:.7em;padding:0 5px;border-radius:4px;font-weight:700;letter-spacing:.2px;flex-shrink:0;border:1px solid var(--bd);color:var(--mu)}
.lt-py{color:#4cc2ff;border-color:#4cc2ff55;background:#4cc2ff14}
.lt-js{color:#ffd866;border-color:#ffd86655;background:#ffd86614}
.lt-ts,.lt-tsx{color:#6cb6ff;border-color:#6cb6ff55;background:#6cb6ff14}
.lt-c,.lt-cpp{color:#c792ea;border-color:#c792ea55;background:#c792ea14}
.lt-matlab{color:#ff9f45;border-color:#ff9f4555;background:#ff9f4514}
.call-bridge{display:flex;align-items:center;flex-wrap:wrap;gap:4px;font-size:.82em}
.bchip{display:inline-flex;align-items:center;gap:3px;padding:1px 7px;border-radius:6px;border:1px solid var(--bd);background:var(--bg);color:var(--tx);cursor:pointer;max-width:190px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.bchip:hover{border-color:var(--ac);color:var(--ac)}
.bchip.up{border-color:#ffb45455}
.bchip.dn{border-color:#3ddc9755}
.bchip.cur{background:var(--acbg);border-color:var(--ac);color:var(--ac);font-weight:700;cursor:default}
.bchip .bf{color:var(--mu);font-size:.88em}
.quick-line{margin-top:6px;border:1px solid var(--bd);border-radius:7px;background:var(--bg);padding:4px 8px;font-size:.83em}
.quick-head{display:flex;align-items:center;gap:6px;cursor:pointer;user-select:none}
.quick-head:hover{color:var(--ac)}
.quick-body{margin-top:5px;padding-top:5px;border-top:1px dashed var(--bd)}
.flow-route{display:flex;flex-direction:column;gap:4px}
.flow-node{border:1px solid var(--bd);border-radius:8px;padding:6px 9px;background:var(--bg);cursor:pointer}
.flow-node:hover{border-color:var(--ac)}
.flow-node.cur{border-color:var(--ac);background:var(--acbg)}
.flow-edge{display:flex;align-items:center;gap:6px;margin:2px 0 2px 10px;padding-left:10px;border-left:2px solid var(--ac)}
.step-code{display:block;font-family:"D2Coding",Consolas,monospace;font-size:.83em;background:var(--code);border:1px solid var(--bd);border-radius:5px;padding:2px 7px;margin-top:3px;cursor:pointer;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;color:var(--tx)}
.step-code:hover{border-color:var(--ac);color:var(--ac)}
.ctx-item{border-left:2px solid var(--bd);padding-left:8px;margin:6px 0}
.tree-line{font-family:"D2Coding",Consolas,monospace;font-size:.84em;padding:2px 4px;border-radius:4px;cursor:pointer;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.tree-line:hover{background:var(--bg)}
.tree-line.cur{background:var(--acbg);color:var(--ac);font-weight:700}
</style>
</head>
<body>
<div id="app">
<div id="main">
  <div id="lcWrap">
    <div id="lcBody">
      <aside id="side">
        <div class="pane-hdr">
          <button id="bProj" class="pane-proj" title="열었던 프로젝트 전환 또는 새 폴더 열기">📂 프로젝트 ▾</button>
          <span class="sp"></span>
          <button id="bWiki" class="pane-proj" title="논문 PDF(.pdf/.pd) · Markdown(.md) 경량 Wiki 연동">📚 논문 <span id="wikiDot" class="tag">0</span></button>
        </div>
        <div class="sidetabs"><button data-st="files">파일</button><button data-st="order">학습 순서</button><button data-st="hot">요주의</button><button data-st="review">복습·기록</button></div>
        <div class="sbsearch"><span class="sbico" aria-hidden="true">🔎</span><input id="flt" placeholder="필터: 함수/파일 이름…"></div>
        <div class="scroll" id="sidec"></div>
      </aside>
  <div class="split" id="sp1" title="드래그해 너비 조절"><button class="spbtn" id="bSpL" title="왼쪽 패널 접기/펼치기">‹</button></div>
  <section id="center">
    <div class="pane-hdr">
      <button id="bTogL" class="ghost-btn" title="왼쪽 파일 목록 패널 접기/펼치기">◧</button>
      <div class="tabs"><button data-tab="ov">① 개요</button><button data-tab="graph">② 그래프</button><button data-tab="code">③ 코드보기</button></div>
      <span class="sp"></span>
      <button id="bPal" class="pane-search" title="전체 검색 (Ctrl+K)">🔎 검색 <kbd>Ctrl K</kbd></button>
      <button id="bTogR" class="ghost-btn" title="오른쪽 튜터 패널 접기/펼치기">◨</button>
    </div>
    <div id="vOv" class="sec" style="display:none"></div>
    <div id="vGraph" style="display:none;flex:1;min-height:0;flex-direction:column">
      <div class="gtool">
        <div class="gtool-row">
          <button id="gBack" class="gnav" title="이전 그래프 (Backspace)" disabled>◀</button>
          <button id="gFwd" class="gnav" title="다음 그래프" disabled>▶</button>
          <label class="gctrl"><span>범위</span><select id="gScope"><option value="unit">현재 함수 주변</option><option value="file">현재 파일</option><option value="all">프로젝트 전체</option></select></label>
          <label class="gctrl"><span>깊이</span><select id="gDepth"><option>1</option><option selected>2</option><option>3</option><option>4</option></select></label>
          <label class="gctrl"><span>방향</span><select id="gDir"><option value="both">호출자+피호출자</option><option value="down">피호출자(아래로)</option><option value="up">호출자(위로)</option></select></label>
          <span class="sp"></span>
          <button id="gFit" title="확대·이동한 그래프를 화면 크기에 맞게 초기화">맞춤</button>
          <button id="gPop" title="호출 그래프를 별도 창으로 띄웁니다 (다른 모니터 이동 가능)">↗ 새 창</button>
        </div>
        <div class="gtool-row">
          <label class="gchk" title="명시적 import·타입 없이 이름 기반으로 추정한 호출 연결을 표시합니다"><input type="checkbox" id="gGuess" checked> 추정 연결</label>
          <span class="legend">
            <span class="legend-item"><svg width="26" height="10" aria-hidden="true"><line x1="1" y1="5" x2="25" y2="5" stroke="currentColor" stroke-width="2" stroke-linecap="round"/></svg> 호출</span>
            <span class="legend-item"><svg width="26" height="10" aria-hidden="true"><line x1="1" y1="5" x2="25" y2="5" stroke="currentColor" stroke-width="2" stroke-dasharray="6 3" stroke-linecap="round"/></svg> 콜백 참조</span>
            <span class="legend-item"><svg width="26" height="10" aria-hidden="true"><line x1="1" y1="5" x2="25" y2="5" stroke="currentColor" stroke-width="2" stroke-dasharray="2 3.5" stroke-linecap="round" opacity=".8"/></svg> 추정</span>
            <span class="legend-item" title="각 함수 박스 왼쪽 세로 막대 색상은 파일을 구분합니다.&#10;(같은 색 = 같은 파일)"><svg width="16" height="12" aria-hidden="true"><rect x="1" y="1" width="3.5" height="10" rx="1" fill="#4cc2ff"/><rect x="6" y="1" width="3.5" height="10" rx="1" fill="#ffd866"/><rect x="11" y="1" width="3.5" height="10" rx="1" fill="#7ee787"/></svg> 파일별 색</span>
          </span>
          <span class="sp"></span>
          <span class="muted small" id="gInfo"></span>
        </div>
      </div>
      <div style="flex:1;min-height:0"><svg id="gsvg"></svg></div>
    </div>
    <div id="codewrap" style="display:none">
      <div class="crumb"><span id="crumb"></span><span id="selBar"></span><span class="sp"></span>
        <button id="bFocus" title="현재 함수만 보기 (f)">현재 함수만</button>
        <button id="bPrev" title="이전 문장 (p)">◀ 이전 문장</button><button id="bNext" title="다음 문장 (n)">다음 문장 ▶</button>
        <span class="muted small" id="lineInd"></span></div>
      <div id="code"></div>
    </div>
  </section>
    </div>
    <footer id="footBar"><span class="add-logo" title="국방과학연구소 (Agency for Defense Development)"><img src="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAANAAAAAsCAIAAACblqFBAAABC2lDQ1BJQ0MgUHJvZmlsZQAAeJyVkLFOwlAUhr+LJILBOMjAwNCBgUWCDsaBCYaGzRRJKE5tKV2gbW5rfAHZGFjZiItvIK/ghomJg5OPQEh0NtdqysLAmb785885/zkgXgCydRj7sTT0ptYz+9rhJwKhOmA5UcjuEvD9nnjfzti/8gM3coA1UJE9sw+iCBS9hKuK7YQbiu/jMAZxrVjeGC0QA6DqbbG9xU4olX8KNMajO7XrLzcF1+92gBxQJsJAp6nuTyzBI1x9wcEs1ew5LCdQ+ki1ygJOHuB5lWrpT0JLWr9SFsgMh7B5gmMTTl/h6Pb/ETuyqXlldAICPEa4aLTxcaihcUGdcy5/AKbWPz8bOFjoAAAt8ElEQVR42u19d3SVxdb33jPPc3qSQyqETigBQgldkQ4CUu3YBblYr/1aQEFRUa6K6FW5V732i4p4qXKRGpGA0kKL0iFBEtKTU3LK88zs749JDoc0eN93fet71/qcdVbWw1Om7Nmzy2/vGZBIwGUVIgAgQiAJiAAADJEBAIAEAgIJIAEQkEHNC3+UP0rdgpfJcEQCAQk1AEAAUnwGJgABMAA9ch+JCExEBGB/0PePUqdol8FrElBDZAIAw4XSe4T8hyGQB+FKFH4ACWghPQYsyejohDHd0NmZMScAAJkAAPgH2/1RLkvCIZBJwAkZyIBZkYXFG9G7H4JlAEGGSITEbYyYRMFECIAIEJhTOluBewgmj2PO7gyAyEBkAH/o2D9KEwxHQGAiWiQZsngtnfsafHs52oBzYhZONiEqZOt7WeIIUZqlpUwSx+Zq3v1Sc6A0QBokQpLZMWk8pt7OY7pJIEYSkNWo4v81haimP/g/szn/S/WYpgkAjDHG2P/zzvzvUakmoUX6DonT7/CyzcAc4OxOgTMMOJpBIUpNS6re6g6szjcr92HbhyhxpFm2mcsQMBuAJC2G8VhZ+IUs20gtpmObu4k7kAxAfvlUk1Jeerkg1pm2SJFSqho45xHSCyGICBE55wCAF/oj/yeLFi+YDZesh2mapcGXozpDTa9MKaXiqoaGf+nOEFGEKZvqKPsv2EKqS01MR2MMhwCSAAAtVPidOPOGFqoQsb2g3YM8doB5ZjGcXyNjMtDVhTcbjtwtK79hnr0UKtSSp0pghvcIr9orQLD2j2NcJpz7mhd8RWf/Kjy7ofML3N4WyASEy3EmELniictgTRMbMBOJMS1q7DWk51yvvSOIwOOplFIwxmJjYxuTB0I0ZnIQImOMSSn8fj8Acs7tdluD9ag5RmReb+W//vUvj8fbv3/f4cNHEkn1PmPM5/OGw2HGWEyMq7GxqyXEmBbtzBERY4xIAoAQsrq6GpFxzux2R4NjQuSXJ/voMjQSAYCUFOmSlAZj/LJUKgGh+oM8nPcO/v4PXZCROJJ3eQV5HAAAGaL6BLd3JKYzAAISRx6DwpXQ410tcaLqHYXPAyGzpiCBRCDvATr2FPpPCVtb7Pq6HpNJZAAybNykk1Iyph0/fuzNNxdZrRYpqUHqSCkDgequXbs++eSTam1Fzy4i7ty5c9++fXa7fdKkSQkJiURSSrly5cqioqK0tLRx464BgGnTbs7Ozu7UqeOaNWtcrlgiUY9d8JLWZ1lZydSp1+bn/z5q1IiPP/5ESrO+1IlUIoSZkZFx5MjRRx97+K1Fb0e/9MwzT3/55b/cbvfy5d+mp3etX4+iDACcPHm8sLAQABITk9LTuwKAlKZ6VF3tmzRp8vHjJ0aMGP7ZZ583NCIoKCg0DIMxbBz9AiKZkpJis9kuR4Ej8l27fiktLUlKSurff6AkkzXuKWoX+B5IEgFq4swbLO+fmiVWSi/pCcjjQAaBMQDOnV2BCGWIUCNRAb6jHLlRmUOJE0GGEBmzNCcAojAAInFwtCSJqMVy47w8/KjZfTGPzQQyALXGVo8acHFx0T/+8Y8mBmq3OwKB6hEjhj355FMAos7EcK7v3r37kUcec7lcQ4cOTUpKAeCcw4IFr+7ff2DSpAnjx09QbxYUFMbHx9dX30SEyH0+z/z58/1+P+datBqSUvr9/quuGjxz5iyXy2UYRn5+XllZWSOL5+iTTz7Jua6QTNOUKSkp23/Kvvnmm4ggGAx16NB+8eLFDoejsLAwHA4rI6/Bqk6fPjV79pxt234sKysnIrfb3b9//5dffrl3795lZaWappmm6fX6zp49W1ZW2ohA4tOnz9i9e7fD4ZRS1Cc+Y8gYC4VC69ev69OnX0PrJ1r8S871rKytkyZNASDGYNWqVcOHjxTCaExIa1FugmBoMX//FM5+wi2xAhGlKY1yAALUEBghIQlCCcABufT9KoNFqNvQcxikH9FOSAAmAiJqRIKQyeqzMligMU0yFxeV5m9PY88Pmb0tkQLqsCHTAQGgdes2f/rTTLvdbrFYNE3jnOu6rmkaIjLGvV7v8uXLCwsLY2PjGqNFYmKiy+VKSIjPzf01EAhJaQohbDabzWaPiYlV79hsdl236LoFsVFD8OOP/1lWVlnnvsPhqq72CSFnzpzFObPb7Zqm6breYCWBQGD16rURC8vhsHPODx06tGfPXnUzPb0LANhsNovFouu6lNI0TSIRmWkpJSIrKDg3deq1ubm5cXGxffv25ZwfPXpk/fr1R44c+fDDD59/fm5pabGm6V6vNyYmhnOtwcWMCEQUDocdDjvnddADQmSmaYbDYcMwLmnnSSkReXl52SOPPGqx6JqmG0b44Ycf3ro1S63hBjlVi4BthBZZuVPmLdaBSAZRhg1He63VdACl1NQfAOBAAhGoai+TAaY5ZDBPBvK4sxtEuwXIGZng6kbt7jNPv8+YIKbp4Tzj2IvQ4x1kViQkpPq6FREBZJs2bT/44MMmRrthw4YzZ85ISY07g8I0TdMUd9xxZ0SAxcTEcM5M06idAEkkiS4YyBdrZ3K5XLNnzykvr0hISOScE0lEFgyGPvnk47y8PJfLpWZRmcz1ZwgRAahdu3Zr1662Wq1JSUlWq1UZhVJKIhBCFhefV5xaWwe53W5N0wC0iOmprLSFC//666+/tmzZctGiNydPnswY++mnbbNm3XvuXMGCBQuKi4tOnz5ltzucTldjXoGi7ZIl74XDIYvFGu1OKWvVarV9+OEHr7/+ptPpvKQtIaXUNG3OnNnHjx+PjY3t1KnTqVOnTpw49fTTT3300cdSmg0aJFqNeEMGZoU4uZARmPFDKVxMpuDdXtWc3YgEINaErWpsPQZkgieHIwJamFEpPQeYsxsSApJ6DQEkAoKutX7AIKL8j9ESb7IY9PxIZz/Htg8QmEisQZ6TUhIJxSV1KKc0nd/vizyVUhJJxlhj1nq3bt3tdpu6zsvLq6ryRD/VNK28vOymm272er333vun2267Q6kDxSuMsccff7J+tUuX/iscDtfvm3KNERFr1igCUGxs3IQJkwBgzZrVu3b9UjsHyBgbMmTI2LHjow1wRFy69KuEhIR27dqMGXO1cgU414PBwI4dOxDxqquuuv76GwCkEGL48JHXX3/9W28tPn78+MKFr6WmpiKyxx9//MCBA01gImlpnZpgo4SExAZ1en1fStMs3377zZdfLrVYLD179vz3v/993333rlq1+ptvlg0dOuzOO+8yzbCmaQ0xHBEgF+f+xav2Usok3v09kNUkg0xLADARFRNhxM1A4BA6g/4zxKwAAhGoci+0uIXwwms1nxABCb31/TJxHOou4T9Nvz4K576gxOHg7AokGlpGNQBVE06qrrsZY0TEOWeM1bq9dVAGAEAp5fvv/61Xr0wiUwgYM2bM2bNno+UZYywYDG7YsME0zZEjR9RncSEMIopgGUIIj6eSSNbvueoMY5Y6nZFShMPm/fff/+mnn9WxXBHxkUf+/Prrb2iasvAAkT333HNCiAkTrhkzZmxE4vr9vlAoRETx8c2EEMo5BRBut5uIpKQRI0YkJ6cAgN1uF0I2wXBSmo0BhJpmMQzjkgCelJJzLS/v9DPPPGuxWK1WfdGi110u16uvvrp7956SkpLnnnt+wIABDbo+GiluC+bJ899wW0tqcz8DBOYA5gQSgLxGVEVFuhC58B1Boxw0O5AEpjNfLpnlTGsWISiqP0jqijvSCEBzp4jmUyDvPXHuK73zSw3F+LG62nfo8KH6Yi/CB4xpgYA/HA5aLBafz3fw4MFwONyxYwe3u1kEZYj+Li4ulnMOwDUNOOfR/ISIhmEkJye9887iYDCYkZGhpFodNgLArKwt+fn5MTGxU6ZMqbXVqM4q8fn8x44dC4VCrVq1bNaspjNCCM71jRv/89VXXyUmJkyYcM20adMQ0TTNTz75ZOvWrA8//Od11107ZMjwWpktJ0yYYBihfv36XrzGdDU0KQXnPBQKE5GuW2vHS8eOHTdNEQ4Hw+Fg4x4oNQEIRwRzxN6IAH4NojyPP/5EaWmZEOKll17MyOgVDgdat26zcOGrd911d1WV5+GH//z99+uUXIiuVkOQBJzOr+L+07LlTSymB5Colfo14fiLcRQQCLJyHyezRnOihUJF4DtC7isBBF4Es0W+NZGAgEGbmVC6GUvXy1bTmaMDkBnhOuWI5efnjx83UQgzAjtFU1xKaRgmImiabrFYcnJyRo0a5fV6v/vu2wkTJkkpI84RImoa13XLu+8uSUlJUTQqLy+32+2R8asKXS7XTTdNi8BadRhOccwHH3z41Vdfd+7ceeLECYhYZxaklA6HY//+/UOHDi0vL//oo4/uvPNOIYSm1TjjOTk5iOhwON54443ExCT1Vfv27YcMGUokDx/OHTJkeGRq33zzjY4dOxEJgBq7m0i4XLEtWrQ4evRoTs4Bv9/ndCrzUf70009WqxURZ86caZoGEYRCQavV2iBsjk0C77rOAUDTNNURXddrtYesT5B3331n/fofNE0bM2bMfffdHw4HGePhcHDq1Otuv33TZ599sWPHzgULXpk378U6HqtWA3CUbeAWt6jYA559ENsHyGwk6E7EdKBqrMohpiNJAJDIuPSR5yC6r1QB1QaBa0ICYFi+G4SPRKUsXoftHsK6/AyapsfEuDRNs9lsipRqkCUlJaZpOp2O+PhmyldQxDVN0aAWCAZDPp+PiBYvXhy5abPZgsGgx+OJDlQQkc/nsdkciNSYM5+UlKzrutvtjuC0daxGZQ66XK5gMFi/My1atJBShkKh5cu/nTbtViJBhCtXrkBkRJCSkhIRMIgUCgWJiEhG+EMBPffee29W1o+//fbbzTfffN1112ua9p//rMvO3mEYxvTp05cvX3727Fmn01nfbIqUoqJChS03hAGBEFLXLZWVlZxzRCgsLExISLJYtOTk5GjzgHP98OGDCxa8arc7YmJcixa9wRhaLLbIC6+88vKOHTvy88/+7W/vDh48ePToq6MVq4aA0nsQAycld2vhIjP/A5axpHEtTggAgVMQPIucK62CQIBoevZbgBrDF2oUsf+EPD5fgwCiXZZtwzb3qFCYYjrGGIBs06Z1VtYWu91us9ktFgsAIfKyspIxY8aeOnVqwoQJ7733nlo0RBAOh4LBkM/nTUlJicgD1fmuXdP/9KeZcXGxCklRA5KSfD5f167ppmkgMr/fHw6HA4FqxpimaU1kaglhCiGUg0lE1dV+wzBCoWDEEKyurh42bOgnn3zq8VTGxycA1MhaxjiRnDp1ypIl7x84cPAvf3l60aK3ONcMwygqOu/3B4YOHTJ69BjVimGYymCvI0Q551KKa6+9dv78+a+88vL336/7/vt1tQCN/aGHHpw9e/aUKZMRUdf1e+6ZuW/fvvqBWkT+4IMP/fTTdqfTqRRILVCCtcpaIoJhmMpFvf/+B3w+/5Qpkz/66J+KY1SwJBConjXrXo/Hi4hvvbWoffu0cDi4c+cvXq8nKSmxX79+bnf8okVvXn/9TV6vd+7cuUOGDLVYLBHFqkkAWbGPSUGaREC0tQRl7DfIc0ogeX5FUY5aLAEBAIFkaGW+X2WokFtTAcwGgleIAIi6nSwuMoKInEJ5svoMd3Wto7QtFmv79mn1cC+nSrTTNM1utwNYVRMOh1NJELW6IuIHQA4ePGTw4CFNG7/vvffe008/zRhardbI53V0pRACgEX0XTgc1nXLZ599GggEW7RoTlTDWERksVgSEhISEhKiO6O0dlJS8vLly+fNeyE3NzcUCgGA1Wrr1KlLv7595s6b63Q6pZRWq8XtjouNja2VslgHniQSTz31l6FDr1q+fHlBwTkASE5OmThxwujRVwPIzMw+tQS01De8lAwLBAKlpaXREU9lZQohEUHXNUSmIE8hRCAQKisri3bqEWum4M9//vNjjz02atSoO+64wzQNTbO88MILWVlZo0eP3Lhxs2GERowYde+9s9av/8+7776n6zrABTNOA5DoPYTIEZjJLKzZVU26KAgAVJnDCAk4gFnjtjIrC1eA9yBYU+tZfZFkJ4GWlujqBqUbyeJmIQ/5joKrK4AE4BcJQ6lcMEVlQOSmaUaSO4lICFPNirJUapUR1vHFhBC6bt20adMPP/zH6/UxxmqhB8YYB6C2bdvdcsstLVu2bEy2MaZZLBoAWK0W5RQ7HC4AuOKKwVHvULQpHYWqXPAniESHDmlffPFFE5R94onH77vvXkS02WwRaV3HqJfSHDToikGDrqiTG6uCmIjMNA0lrevYBogIIF59dcHzzz8fFxdrtzsQUQhT163vv//u22//LT4+fulXX3bq2FnJfsMwgsGAx+ONiXFFL0VE1HXtlltu7dMnMyYmhkgiAmOsRYsWnHOn0wkAnGtSirlzn5s9+5mYmLg6JqAGRrkMl3FkFC6VWgpzdoqACvXj+oBcCo/0HWbcAhcmScU7w1S1HxLHNeFNE3AW11+UbOSGH0BS4FRjMZwDB3IeeOBBm80mpQRA0zR8Pl+zZu5t27aNGjVS8Vk4HE5JSV66dKnd7myQY3Td+te/LnzhhfmhULARI5otXLjw888/HT9+Qh0HXqmAEyeOnz592jDM48dPOp1Or9ezYMErwWCoqqrS5/MFAoFAIOT3e/Pzz1qtVuWW1kcElSYKBqufffbZsrJyi8VS2xkyTAOBKW2lPiSi+fNfbN26bYNhUMZ4OByaN29efn5+u3bt5s2bxzlnDGvbZYhYWVkRDAarqirrQ9A9e/auT4T4+ASlx1u1atWiRWqDExfpicIahQh36dIVgEzTACAhhGGEpZRCkBBCcaHVarXb7YYRqmPvamSWM6PU1JvJpGt4/HCwJjc41FqFD9J3HEJnkekXyW1CYJw8uYLCDHVsKE5KyBEEtJiGjk6iYCkrXYfBkvq6o9bkD+7YsbPW9kJEtNmsiOj1+k6dOlWLNomWLVMb5CTFtQcPHnjttYU2m7VXrx533nmH0+lSqQBExLl27tzvH3/8cUFB4bPPzr7qqqtcrthoVEUBm//4xz/eeONNl8ulzKOzZ3+fM+e5+s2lpKQwxhoLBanJtlqt33+/7vjxE02kA1mtNinF448/0bp1nZjHBZvdYrHu3btv48aNGRk95s2bF8kTISLFGQ8//OeCgoKOHTvWA4lQSjO6WgW8mWbNdIdDRq32qDEh6mccqSye2qQbjMCTmqYpbasQqOg1XydhR2PCT6ZPuvtbOsxWSguQmkhWQc9eJoOEbgDjAlSCApidVR+XgVPMkQ4k6ju5CmJhxNE9SNhcsmwDiFICqONnqOnp3LnL0qVfWa261Wq1Wq1RGT6ohPZrr726Y8dOhQ40wnDw448/hkIhm822cOFfhw4d2kBcT9Pmzn2hoKDg2LFjffv2l7LuHCsMJSUl2Wq1Op3OmJiYuLg4l8sVGxsbGxsbExMTFxcbExP31ltv5ebmXhIvfeWVlysqKpxOlxJpdWJE69atW7NmrdPp1LRL5GXFx8dbLBa3O85isUItAVXjmsZnzJjZWH5RHTVdR/Yos0TJy/pjUXK6tLRk79690fqaSHKulZaW2Wy2ysrK7Ozt0ai48kIyMronJiapBaCBFAACAZAMJBKMs0akDgAHkNK7nxMCCqQIBIJIEpCTWQVVB9GRTsp1BWwg2Q5NJMZNIYELEtiIPGjWLP6WW6Y1QfSPPvowFFIB5kanWRleAFBSUtzgC+Xl5Yri9ePunHMAedttt40bN75Vq5axsS673WGxWBqEsj755BMhxCUYDunGG29u4nlhYcE33yxzOByXjJoLIaSU4XC4oOAc51odSVar1DApKamxfIL/RlEY5+HDuddcM8Fut5umsrNJhfyVAs3JyRk9enQUt6Gu6x6PZ9WqlZMnT1E1aIBMAgJogDohMRINQxskCTUyzoPvBHALUDTgVhs/RQLPfmpxU+1Wrgby1gE0Qk6aC4Ah6Y2wJkRiqY2pSymlrmuNwWZqKY8ePdrtjvP7q2fPnrN1a5bT6VQzoQymoqKiTZs2m6bRtWufLl261pk2dd2lS3pdM5REJE6v2J1ICGE2KBUuXm1MRcnqv2aapqbpoVBI1/U6DkdjAQOr1Xru3LmhQ4c1psRN01i1amXPnr2bzi9Ss1bbd2o6rRkAXC5HampqbGysxWKxWPSoSanRP9GdNwzDNM2ioqJovtckd5AWg/5fwwWf86TJTI9tFBMBkN5cFioEzQr1VyEBMB09v5LwAHdhA1wkAZiUPlmxE0s3AJikO7Hx4TXGTApX8/t9gUB1VZUKazbAcFKaHTp0fHvx4kcefez06dPvvfdeQyLQmp6e/s47f7NarQ1OTMToiWAc0TRVWkZKME3TNE3DMJpmlMZGpGzKYDDo9/sjmx6aKIZhKCEXQbDrxZ0gGAwYxmVtADUMIxQKqUDtpTLOZY8ePX7+eYeycywWS51Ny3XCZuFwOBwOBwKBZs2aRYBJNEMF4sB0PVQgRdiM6aH1+DvXm9WPaEmSgBqdfh3Ofoi6GxryChHQJGI9PuKxmVCTY1JHNGmiYCkcm6NpcZL8MnWmnvZ041GNRtc3Itu0adOZM2eaNYubPHmKrlsaXJ21SYsnt2zZEg6HEHn0a0LIhISE8ePHx8W5LykGmu5Pbu6vXq+vWTN3ly5d/hs7V9SI9u7du2fPHqvVNnnypPj4+IbiwjVkPnLkSCBQbbfbdV2r6xEDCNM0DBEIBLqkd45xxTQoU6Pbzc/Py88/q+t6jx4ZDoez8XYvNwW6MZ1c872QQXngHubbD5pTGl7s8TF3D2qQCQhM88C93PszcBc0JFcQuBBVst3TltYzoP6WGSKJHI49S0UrmJ5I4VLqOJen3gqNbK5pOtIcpbKbSr2PpGU3aZ2YCp5tLMepkQ0KGNW9hvetKMPuslmZ1Z+eBpu+5IguWc/F2ZGXbrde3iX+F5fTBbWgIVpFbGfm2QXg4pKZVT9z96B6rCYRNAoWYPUxwIb0aQ3wQQwYVe2Wracz4HXrQA5muag6jNxGFJLMAc4u0KiDUhNpbgyjkdJUI296r43SrY2ZgxHYLGrPjrwM8l3YhKJg3ojmrZdpol/+lrDIiJrg+6impWEYTY+9cbMSGdMiCzViLl/mrqXLVwW1y+Ni1xgBeGx/iToAEROiYo+sEW8UnSFCAOQ5hEYFMEujEoUAuM78JzB8vqFdqBIAJUcmTKCQtLVizrQGQWZlhZSVlZSUFEU8GKIa70wVhaeryEzEhFePIneix6wgInWhaRpjTAFKClYoKipctWplSUmRSqFTDUVvgIuu8/z5glOnTpw4cSwQ8HOuq/qjIx+qUcMwN2xYf/Dg/sbqjGxkrL8AVCXRn9R6sudOnjx+4sSxYDCocpMicHH0XtfI/Uh+UXQHqqv9hw4dCAYDkc2UkXVbv2PRJK1Dhzo9rP8tImdMq3Vmo8Qpj+0trSkoQ4LH6i2uZcihIbhBevYQSqSmBbguw6XCf+TCfpgLoS3JtGZ6h2dIc5MIYNwA1NwN5mASASKbPv2eUaPGhMNhFdFCBM51xjT1iygXznVEFVfm6pG6E5FG6iuVgB/9ISJXN/1+/6RJU+bPfyk//6xSwZFPVHRLVYLIpRSI/M9/fnjs2HF33313Zmbm+++/q+pRbyplp6qdM2fO3XfP2LnzZwXvqTprOUOL9DayWmp7ziN7CqO7oWh43333jx8/4a677s7M7PPBBx/UdqnmzUg9EewmMsyoQeG5c+fGj59QUFAgJTQ42OiORZGUR+hQYx9F0bbOt6ZpArC9e/fcf//9iBzgQhoiIzLA0gKbDYNgKUseiynXU117nwA5SR94DjPUJMqmLEoEBj6qOlAvRVECEpGkuJ7SmijBhs0nNKhupJSM8RMnjuXl5VVXB7Kzs2sCuARZWVt27/4lP//MiRPHlCO7c2f2xo0/mKaByPPyTp8+ffLYsd/UHfWCx1O5bt3anJy9jGmFhedycvYqRZObe+jMmVMAGAqFsrOz8/PP/v3vS7p3z2CMnz59cs2aVUeP/qZIefjwwaKiws2bNx49ekStT4/H9+CDD23cuHnRokWzZ89Zt+57xjQhxNatm7dtywJgnPOCgoLvv1/3yCOP3HrrrYxhMBhcv37d3r27ETkR/PZb7vnzBTt3Zu/a9bO6g8j37t29du3q8vJSNbWGYWzYsP7nn3dEmBgA/f7qBx98cOPGzQsXvvbUU09t3ryJMd00jS1bNm7fvk11b8+eXWVlJURgmuaePbsqKsoY006cOLZmzarz5wsYQ0SmAvyMsd9/z1+zZtXBg/sVhx0+fLCsrGTnzuyff96hOFURatOmDX6/t6KidP36dR5Ppco2LC8vXbt29ZEjv0YIVVxcuHXr5tzcQ5pmCQQCOTk5a9euPXXqZCBQfUGsSGFKIsO7P7i9t7FrnBnMJ2mSDBOZRCaRIDKISHgPGNv7ie39zR19RHbk17f2V/NPM7uf+VP38P7bJYWJFGoliEyqLcbZT83NbUOH7pVkkBS1TVz4GUaYiF57bcGMGTNeeunlGTPuJqJQKDRt2rROnTrdcsu0Vq1azZw5k4hmzpzZp0/m0KFDx48fGwqFlix5Lykp8dprr01PT580aaIQ5pEjv3Xr1nXkyJEdO3acN2/eb7/lNm+e/Pvv+UKYnTt3/O67b4lo//59PXv2aN26dadOnbKytq5ataJVq5bjx49r167t4sWLiWjIkCFdu6YPHNj/vffeVVrj6qvHfvDBP9RwHnrooWnTphmGMWXKlCuuuGLgwAF33nlnOBy+5Zabmzdv3qZNmxdemFtcXHTFFQNGjRqZkZHx3HPPEdHNN9+cltZh6tQpqanNFyx4mYief/65zMzMcePGtW7dcs+eXT6fd8SI4cOHD8vMzHzssUeJyDTDRDRq1OhI09On3z1z5j2hUOiaa8ZfddVV/fr1u+eeGUQ0YsTwp59+Skq5Y8f2lJTkkpLiZcuWderUady4cd26dcvJyTl37vdWrVoVFhZs2bKlXbu248aN69Chw7x584jo6quv7tu37w033JCamjpnzmwiGjCgf2Zm7759+w4ePPi6667r0qXz8OHDhBD79+/v0SNj3Lix6emdP/74n0Q0YMCA3r17XXPN+OTk5DVr1uzbty8tLa1du/a9evXcvn1b7RAEEAmSBhEZR58ztrQIHX9BjUfW/FXMR0bBl+aPnUX2AJHdR+zoJ3f0FzsyxfbeYnsvkd1bZPcTO/qI7D5mdl+RnRneMUhUn1KfS2lKIuE7KkJFZui08cuY8I8Z4YqfiIikUYfbFIiqqLZs2bcnT57s0qWLYYRzc3OTk5OPHj1CRBMnTrz//vuPHTuakJBw8uTJYDDYtm3rFSu+W758Wdu2baqrqysqyhMSEg4fPvjEE4+NGzeWiHJzD//znx8R0bBhQ7744vNDhw526dLJ7/dJKUzT/OWXn1u3bn348EHTNLp16/r2228T0ddff92uXftwODR48JWzZv1JEUPN+tVXj12y5H0ppWEYixa9MXny5I0bN7Zt29bj8RQXFzVvnrJ+/X98Pl/v3j3ffPONYDA4d+5zV155hRBi9+7dbre7rKz0jjvumDJlKhEtW/ZNu3ZtDSOckdH94YcfJqING344ezb/739fkpGREQ6Hjx07lpCQsG/fHjUpo0aNXrJkiWr6pZdevOuuu77/fm2HDh38fn9BwbmEhITc3Nxvvvk6M7M3Ec2d+/zEiROIKD09/Z133iGie+6557rrri0uLmrVqtX58wVXX331E088TkRZWVkJCQmVlZUTJ06cMWMGEa1evSo1NbWqqrJ//35qpSUmJn722aehUCgpKen48WPTp0+/9dZbiejzzz9t06ZVMBjo37//M888TURz58694opBQohvv13WtWt6eXmpYYSlrJEsWiSVnLWZLst+5EVrDTCZaQoA3vEJriUSCUCgyoOIgAgESNIPJkhuA80JaAEZBOFFaSLXkVkIGQtXSc9hsLdHKSSzUNl/xJG5XHODboXgGUi5UXNfqXIKGkQx8vLOHD6c+/rrf3W5XHl5efv359jtjrg4d8eOHQEgLa1DKBQqKSlmjD/wwANCCJfLRUTV1dVduqTb7Xa73Z6WllZcXFJcXDxw4EDTNLt1696tW3cAmDZt2pYtW8+cyb/iiisdDmc4HLRYbHFxcQCUlJREJKurg4MGDTIMo3//fk6nw+fzMIYjR44EAJX5E+3YaJp27ty5pKSkQCBgmuLGG28QwkhKSqyoKHc6nYwxl8thtVq9Xm9JSenYsWMBqG3btpWVlVKKvn37AECnTp2kJI+n6ssvv/zLX57MzOx1ww03jhgxsqyszOervuaaawCgZcuWJSUl0Tu7apsuiIuLraqqDIVCU6dOIaIWLVqcOXNq8uRJzz47Oy/vzI4dO++++04islj0ZcuWrVq1yuv1ZmRk+P0+TdPC4XAwGOzdu7dhGOnp6fHx8QpGHjz4SiFEx45pDofD5/NwrqWkJCNiampqy5apFoslPj6+vLzcMMIHDhwYM2aUYRjt2rXz+by6rvXpk0lEGRndV61ayRhzu92IzO2OU/uUo7cJIpBgtg6i/YNwdD4vXCHR1ExhGkWQ/hroiWiUgX8vcpeU1SSJYgdi4mCI6c2szYlZ0Kym6tNQuVuWZ0HgJOdxBAhVuyFlkkQOpZvo2As6hKQs4/5qw96Rt39QIYAA/MLphlFB91WrVqemtnzkkUfUlpZ//WvpwoV/ra72/eUvTw0efOWKFStvvPFGlytG17UPP/wwKSnphx/+M3DgoLVr1yg+ACAVtouLizt69JimaR5P1d69e4cNG3bjjTctXfp1VlbWJ598HEHRhBCM8VAoxLmmafzo0aMDBgw4ceKEz+ez250AqEII0UFuq9XGGDt58sRnn33x6aefcs5jY2O++uprXeebN28eMKC/4gkhJABpmtahQ4cVK1Z4PJ7s7OzWrVsbhqEMbcMwGOOGYcTHJ6xcubKoqHjixIlCGK1atWnePHnlyhWhkLFtW1bfvn3VllhEtFqtjLEjR3775ptl3377TUVlhdvd7NtvlzOGW7ZszszMtNkcgwYNfPXVheFwaMyYMWqj0KxZs2666aacnBwV+lRRTs75qVOndF0/f76woqLC5XJJKQ8dOsQ5Ly4uqa6uttsdKvKh3E/DqLlQAd8hQ4YsXrz47Nm8I0eONGsWH8n1N4yabMVgMCilRNQa2giNjMjUmt9oeI9i4VKmx5MmtYps49dn9F4fkf8EBkuAQqarF299r5Y4BCEqKqwD2dtBwghoMyN0fpk494VFhE3fUZ0MChfQsRc0GSBuZ2SGuYt3ep5bUoHM2tMeLtpvp3KpP/300xtuuO62224DAJcrZtasWfPnz9+0adNLL738yy+/9OmTWVxclJHRo0+fPrfffnv79u137Ni+fv0Ppmn6/X7FFtXV1V6vZ9ase8eOHTtt2s0nT57s2LHTsGHDEhISBw++ctmyZYMHD45s0JJS+HxewzAQ2UMPPfTss89u2PDD9u3bb7vtNpvNXlFRUSfWpGnslVde+fe/vzt48OD11183YcKE8vKKhISE22+/1e12HzlyZMWKFYjo8/mEEAB45513TZs2bcaMGR5PVThsTJ482e/3q/R0KaXXW6Vp2nPPPbd9+/YRI0YKYbZu3Wby5Klvv/3OXXfdLYQsKysdOnSI8tMZwwULFnz33bcHDx687bZbR40aU1x8PibGdccdt9vttjNnzvz73yuI4Kabbpw69bpZs2YmJzcHoJkzZ7700vwff8zKzs5+9NFH27VrW1lZCYAPPPDAww8/dPz4sd2799xww/XNmjWzWCw//LDhT3+6Z9OmzRMnTmjWLKG8vEzB136/T4WMfT5fMBh88MEHb7vttvvum3X8+PHOnTtPmDDJ6/UqQpmmoWJ0aWlpPp/vmmvGv/jiC/37D1DnBkWfD0dESDJkHH1MK92KFjcKn+nso/X+XOYvkSdfozYP6O0eRB4DZAAIQK2WVwiUyYc6Qyb9B+WRl6V/P++7mlnizX3XMxlgREKYsvOLespUaOo8GzRNY+vWrb169YqPT0DEcDiYlfXjlVcO3rdvr91ui41133zzTdOmTZsz5/lAILBu3brS0tIxY0Z16NDx5MnjJSUlAwcOAqDt27enpaWlprY6efL4li1bEhISpkyZQkQHDx565JGHhwwZsmDBa0IYKmnR46natWvXlVde6XA4ANiuXb/s3buvW7duw4YNIxLbt29v3759q1ata4O2mJOzNy8vn4g6dOjQu3cfIoHIvd6q1atXhULhCRMmpKS0IJLbt//Upk2btm3bAWBh4bl169apk3ViYmJ37folLi6uS5f0ysqKPXv2DB06FJFt3LjhzJnTPXr0HDJkGACUlZWsWfM9Y2zKlMlxcW4iE5Hv2bP799/PEkFaWlrPnr1V01VVFatXrzZNc9KkSYmJyQAUCFRv2bKle/fubdu2U5tCduzYvn///h49egwZMszv9/78886BAwe5XLEHDuTs3LmzQ4f2Y8ZcjcgHD75yypSp6enpoVDw2muncq5t2/Zjp06dUlNbZmVt6date3Jy8pYtW3r27JGYmHL06G9bt25t0aLFxImTGGPbtv3YsWPHli1bnTt39uTJU0OHDgVgu3fv3r1799SpU1NTW6ig2UUMB0SEnITfPPo0K81iSCJ5Eu+yMHx4lhbbh7e5LxqdQ7gIQiMVISFByEH6zAP3YfLVvPkU2jMVzSIDbCxttt78BkkGAw5N51XUPBa11wgAb7zxVyU5Bg8e/OKLL1qtNow6+UuRPuorFn2mENSc8eG/5ZZbnE7nkiVLYmJioxLtWSREpqC7qDqhNp1QRqPb0eGB2t0l/KLzkKM+bOhppM7IFu7oGKVQQMnFn9SJoTXRNEbVJmsxM61e6xfRR10//vijw4cPnzx5atSQWS1VL+rzxbSlqH0CFwZ1cd9kAydgEhCqA5QoIE8ugsKloDkobhDE9tJbzaSKHcbZf3JHa3D3Y84ezNZapWoSAYApvYfA95uozBZhj6XLq6i7zWPzWPgcePZLa2vW8XmeMALJJGQAhE1ynBAiGnCvjXLyeplCFNnToEgfCaREaohA7bUVXjQTF++15HWO+4uA73ViRA2eBxjpTKTn0R/WeRq5VvdVQ2pLWKTO+hVeftN1aBgJGERCEZHxRg82wh9CGJHhR+qpf9EYoaIHVXsQx4WcqzpHrhIAI5BADBHN8ytk3tus+ji5ukNMBlXs1MxyICZBSkcPrc8njMUoa8woXgm/zWFMIjAgMhxpzNGBlW8hMyCSRmvtn+aO9kQGXvYJmE3Em+uQ8r9RzyVz1/6/LZdKmID/K2f8EhASSCBEjcIF4uznUPQtCxVz3S25HZAhoZAB7P4uixsIYJAMikOzuP8ocheQlCBY2CNlkGL6UZs7taTJhAz/OFr6j9L4odJIYCJxIgFMJwCqPi5KVkNJFgucBjIZACCXlhTQ4wEkyiAFf+ckJBgAQMwt4nppSRMxYSRoMQgSL5wo/QfD/cFwTf7HIAQEJBF1ABCiEjyHwHNQ+k9g6BwYFST9ABLBgnqM1JLB0QZcnVjsAObsVGOl1Rwdgn9w2x/lv/Q/0dQ6sBdOnqkmUQ0yRCQQLahZgTsRLFRTqQSQgPgHk/1R6pT/A6JF+S9pofKwAAAAAElFTkSuQmCC" alt="국방과학연구소"></span><span class="brand">Code Tutor</span><span class="sep">·</span><span class="ttl" id="ttl"></span><span class="sp"></span><span class="fgrp" title="영역별 글자 크기 조절"><select id="fontScope" title="글자 크기를 바꿀 영역 선택"><option value="all">글자: 전체</option><option value="l">왼쪽</option><option value="c">가운데</option><option value="r">오른쪽</option></select><button id="bFontDn" title="글자 작게">A-</button><button id="bFontRst" title="글자 크기 초기화 (100%)">100%</button><button id="bFontUp" title="글자 크게">A+</button></span><button id="bTheme" title="테마">☀/☾</button><button id="bHelp" title="도움말 (?)">?</button></footer>
  </div>
  <div class="split" id="sp2" title="드래그해 너비 조절"><button class="spbtn" id="bSpR" title="오른쪽 패널 접기/펼치기">›</button></div>
  <aside id="tutor">
    <div class="pane-hdr">
      <div class="tuttabs"><button data-tt="tutor" class="on">🎓 1:1 튜터</button><button data-tt="var">🔎 변수 추적</button><button data-tt="flow" title="실행 흐름·구조">🗺 흐름·구조</button></div>
      <span class="sp"></span>
      <button id="bLlmCfg" title="내부망/로컬 LLM 연결 설정">⚙ LLM <span id="llmDot" class="tag">정적</span></button>
      <button id="bAi" title="AI 해설 표시/숨김 (a)">AI 해설</button>
    </div>
    <div id="tutChatWrap">
      <div id="tutTop"></div>
      <div id="tutThread"></div>
      <div id="tutInput">
        <div class="chat-box">
          <textarea id="chatIn" rows="2" placeholder="궁금한 점을 물어보세요 (예: 여기서 왜 이 변수를 쓸까?) · Enter 전송"></textarea>
          <div class="chat-bar">
            <span id="chatTarget" class="tag">전체 함수</span>
            <span class="sp"></span>
            <select id="tutLevel" title="설명 수준">
              <option value="beginner">초보자 눈높이</option>
              <option value="concise">핵심 요약</option>
            </select>
            <button id="bClrChat" title="현재 함수 Q&A 대화 비우기">비우기</button>
            <button id="bSendChat" title="질문 보내기 (Enter)" aria-label="질문 보내기">
              <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"><line x1="12" y1="19" x2="12" y2="5"/><polyline points="6 11 12 5 18 11"/></svg>
            </button>
          </div>
        </div>
      </div>
    </div>
    <div class="scroll pad" id="tutc" style="display:none"></div>
  </aside>
</div>
</div>
<div id="pal"><div class="box"><input id="palIn" placeholder="함수·클래스·파일 이름 검색 (Enter: 이동, Esc: 닫기)"><div class="res" id="palRes"></div></div></div>
<div id="help"><div class="box"><h3 style="margin-top:0">단축키 & 사용 팁</h3>
<table><tr><td>드래그 / <kbd>Shift</kbd>+클릭</td><td>여러 줄 묶음 선택 → 자동 맥락 해설</td></tr><tr><td>왼쪽 <code>S1</code> <code>S2</code> 배지</td><td>논리 단계(Step) 단위로 묶어 보기</td></tr><tr><td><kbd>↑</kbd> <kbd>↓</kbd></td><td>이전/다음 줄</td></tr><tr><td><kbd>n</kbd> <kbd>p</kbd></td><td>다음/이전 문장 (여러 줄 문장은 한 번에)</td></tr><tr><td><kbd>[</kbd> <kbd>]</kbd></td><td>이전/다음 함수</td></tr><tr><td><kbd>Alt ←</kbd> <kbd>Alt →</kbd></td><td>이동 기록 뒤로/앞으로</td></tr><tr><td><kbd>Ctrl</kbd>+클릭 / 더블클릭</td><td>호출 대상(정의)으로 이동</td></tr><tr><td>변수 클릭</td><td>그 함수 안의 모든 사용 위치 강조</td></tr><tr><td><kbd>f</kbd></td><td>현재 함수만 보기</td></tr><tr><td><kbd>a</kbd></td><td>AI 해설 표시/숨김</td></tr><tr><td><kbd>1</kbd> <kbd>2</kbd> <kbd>3</kbd></td><td>개요 / 그래프 / 코드 탭</td></tr><tr><td><kbd>Ctrl K</kbd></td><td>검색</td></tr></table>
<p class="muted small">녹색 '정적 분석'은 코드에서 직접 계산한 확실한 내용, 파란색/노란색 'AI'는 연결된 LLM이 생성한 맥락 해설입니다.</p>
<button onclick="document.getElementById('help').classList.remove('show')">닫기</button></div></div>
<div id="llmModal"><div class="box">
  <h3 style="margin:0 0 8px">⚙ 내부망/로컬 LLM 연결 설정</h3>
  <p class="muted small" style="margin:0 0 10px">OpenAI 호환 API(`/v1/chat/completions`)를 연결하면 드래그한 코드와 꼬리 질문에 대해 실시간 1:1 답변을 제공합니다. (웹 서버 모드 `--serve` 에서 동작)</p>
  <label style="display:flex;align-items:center;gap:6px;margin-bottom:8px"><input type="checkbox" id="cfgUseLlm"> 실시간 1:1 LLM 튜터 활성화</label>
  <div class="frow"><span class="small muted">Base URL</span><input type="text" id="cfgUrl" placeholder="http://localhost:8000/v1"></div>
  <div class="frow"><span class="small muted">모델명 (비우면 서버의 첫 모델 자동 선택)</span><input type="text" id="cfgModel" placeholder="예: Qwen2.5-Coder-32B"></div>
  <div class="frow"><span class="small muted">API Key (필요 없으면 비워둠)</span><input type="password" id="cfgKey" placeholder="sk-..."></div>
  <div class="frow"><span class="small muted">extra_body (JSON, 선택)</span><input type="text" id="cfgExtra" placeholder='{"chat_template_kwargs":{"enable_thinking":false}}'></div>
  <div id="cfgStatus" class="small muted" style="margin:8px 0;min-height:18px"></div>
  <div id="prewarmBox" class="small muted" style="margin:4px 0"></div>
  <div style="display:flex;gap:8px;justify-content:space-between;align-items:center;margin-top:10px;flex-wrap:wrap">
    <button id="bPrewarm" title="함수별 기본 블록 해설을 백그라운드에서 미리 캐시에 생성">⚡ 전체 기본 해설 미리 생성</button>
    <div style="display:flex;gap:8px">
      <button id="cfgClose">닫기</button>
      <button id="cfgSave" style="background:var(--acbg);border-color:var(--ac);color:var(--ac);font-weight:600">연결 테스트 및 저장</button>
    </div>
  </div>
</div></div>
<div id="projModal"><div class="box">
  <h3 style="margin:0 0 6px">📂 프로젝트 선택 및 열기</h3>
  <p class="muted small" style="margin:0 0 8px">한 번 열었던 프로젝트는 아래 목록에서 클릭 한 번으로 즉시 전환됩니다. (원본 코드 폴더는 수정하지 않고 <code>workspaces/</code>에 저장합니다)</p>
  <div style="display:flex;gap:6px;align-items:center">
    <button id="bBrowseProj">📁 새 폴더 찾아보기…</button>
    <input type="text" id="projPathIn" placeholder="또는 폴더 경로를 직접 붙여넣기" style="flex:1">
    <button id="bOpenPath" style="background:var(--acbg);border-color:var(--ac);color:var(--ac);font-weight:600">열기</button>
  </div>
  <div id="projStatus" class="small muted" style="margin-top:6px;min-height:16px"></div>
  <div id="projList"></div>
  <div style="display:flex;justify-content:flex-end;margin-top:10px"><button id="projClose">닫기</button></div>
</div></div>
<div id="wikiModal"><div class="box">
  <div style="display:flex;align-items:center;gap:8px">
    <h3 style="margin:0">📚 논문 PDF(.pdf/.pd) · Markdown(.md) 경량 Wiki</h3>
    <span class="sp"></span>
    <span id="wikiMeta" class="small muted"></span>
  </div>
  <p class="muted small" style="margin:0">프로젝트 내 <code>papers/</code> 폴더를 자동 탐색하며, 외부 폴더나 개별 파일(<code>.pdf</code>, <code>.pd</code>, <code>.md</code>, <code>.txt</code>)도 추가할 수 있습니다. 질문/해설 시 관련 2~3개 문단만 0.01초 내로 검색해 참고 근거로 주입합니다.</p>
  <div style="display:flex;gap:6px;align-items:center;flex-wrap:wrap">
    <button id="bWikiAddDir">📁 폴더 추가…</button>
    <button id="bWikiAddFiles">📄 파일 추가…</button>
    <input type="text" id="wikiPathIn" placeholder="또는 폴더/파일 경로 직접 입력" style="flex:1;min-width:180px">
    <button id="bWikiAddPath">추가</button>
  </div>
  <div id="wikiSources" class="small muted" style="display:flex;gap:6px;flex-wrap:wrap;align-items:center"></div>
  <div style="display:flex;gap:8px;align-items:center;flex-wrap:wrap">
    <button id="bWikiScan">🔄 텍스트 추출·인덱싱</button>
    <button id="bWikiBuildLlm" style="background:var(--acbg);border-color:var(--ac);color:var(--ac);font-weight:600">✨ LLM Wiki 요약 생성</button>
    <span id="wikiStatus" class="small muted" style="flex:1"></span>
  </div>
  <div id="wikiDocList"></div>
  <div id="wikiPreview" style="display:none"></div>
  <div style="display:flex;justify-content:flex-end"><button id="wikiClose">닫기</button></div>
</div></div>
<div id="ovGraphModal"><div class="box">
  <div style="display:flex;align-items:center;gap:8px;flex-shrink:0">
    <h3 style="margin:0;font-size:1em;color:var(--ac)">파일 의존 관계</h3>
    <span class="muted small">(위 → 아래: import 방향 · 휠: 확대/축소 · 드래그: 이동 · 클릭: 열기)</span>
    <span class="sp"></span>
    <button id="bOvPopFit">화면 맞춤</button>
    <button id="bOvPopClose">✕ 닫기</button>
  </div>
  <div style="flex:1;min-height:0"><svg id="osvgPop"></svg></div>
</div></div>
<div id="toast"></div>
<div id="tip"></div>
__DATA_TAG__
__FILES_TAGS__
<script>
"use strict";
const D = JSON.parse(document.getElementById('ct-data').textContent);
const U = D.units, FS = D.files;
const FD = {};
function fdata(i){ if(!FD[i]){ FD[i] = JSON.parse(document.querySelector('.fd[data-i="'+i+'"]').textContent); } return FD[i]; }
const $ = (s, r) => (r || document).querySelector(s);
const $$ = (s, r) => Array.from((r || document).querySelectorAll(s));
const E = s => String(s == null ? '' : s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
function sanitizeTex(s){
  let t = String(s == null ? '' : s)
    .replace(/<!--\s*Start of picture text\s*-->[\s\S]*?<!--\s*End of picture text\s*-->/gi, '')
    .replace(/<!--\s*(?:Start|End) of picture text\s*-->/gi, '')
    .replace(/<br\s*\/?>/gi, ' ');
  const map = [
    [/(?:\\|\|)(?:rightarrow|rightattow|longrightarrow|to)\b/g, '→'],
    [/(?:\\|\|)(?:leftarrow|longleftarrow|gets)\b/g, '←'],
    [/(?:\\|\|)(?:leftrightarrow|longleftrightarrow)\b/g, '↔'],
    [/(?:\\|\|)(?:Rightarrow|implies)\b/g, '⇒'],
    [/(?:\\|\|)Leftarrow\b/g, '⇐'],
    [/(?:\\|\|)(?:leq|le)\b/g, '≤'], [/(?:\\|\|)(?:geq|ge)\b/g, '≥'], [/(?:\\|\|)(?:neq|ne)\b/g, '≠'],
    [/(?:\\|\|)(?:approx|simeq|sim)\b/g, '≈'], [/(?:\\|\|)equiv\b/g, '≡'],
    [/(?:\\|\|)pm\b/g, '±'], [/(?:\\|\|)mp\b/g, '∓'], [/(?:\\|\|)infty\b/g, '∞'],
    [/(?:\\|\|)partial\b/g, '∂'], [/(?:\\|\|)nabla\b/g, '∇'],
    [/(?:\\|\|)sum\b/g, '∑'], [/(?:\\|\|)prod\b/g, '∏'], [/(?:\\|\|)int\b/g, '∫'],
    [/(?:\\|\|)notin\b/g, '∉'], [/(?:\\|\|)in\b/g, '∈'],
    [/(?:\\|\|)subseteq\b/g, '⊆'], [/(?:\\|\|)subset\b/g, '⊂'],
    [/(?:\\|\|)forall\b/g, '∀'], [/(?:\\|\|)exists\b/g, '∃'], [/(?:\\|\|)propto\b/g, '∝'],
    [/(?:\\|\|)times\b/g, '×'], [/(?:\\|\|)cdot\b/g, '·'], [/(?:\\|\|)(?:ldots|cdots|dots)\b/g, '…'],
    [/(?:\\|\|)(?:varepsilon|epsilon)\b/g, 'ε'], [/(?:\\|\|)alpha\b/g, 'α'], [/(?:\\|\|)beta\b/g, 'β'],
    [/(?:\\|\|)gamma\b/g, 'γ'], [/(?:\\|\|)delta\b/g, 'δ'], [/(?:\\|\|)zeta\b/g, 'ζ'], [/(?:\\|\|)eta\b/g, 'η'],
    [/(?:\\|\|)(?:vartheta|theta)\b/g, 'θ'], [/(?:\\|\|)iota\b/g, 'ι'], [/(?:\\|\|)kappa\b/g, 'κ'],
    [/(?:\\|\|)lambda\b/g, 'λ'], [/(?:\\|\|)mu\b/g, 'μ'], [/(?:\\|\|)nu\b/g, 'ν'], [/(?:\\|\|)xi\b/g, 'ξ'],
    [/(?:\\|\|)pi\b/g, 'π'], [/(?:\\|\|)(?:varrho|rho)\b/g, 'ρ'], [/(?:\\|\|)(?:varsigma|sigma)\b/g, 'σ'],
    [/(?:\\|\|)tau\b/g, 'τ'], [/(?:\\|\|)upsilon\b/g, 'υ'], [/(?:\\|\|)(?:varphi|phi)\b/g, 'φ'],
    [/(?:\\|\|)chi\b/g, 'χ'], [/(?:\\|\|)psi\b/g, 'ψ'], [/(?:\\|\|)omega\b/g, 'ω'],
    [/(?:\\|\|)Gamma\b/g, 'Γ'], [/(?:\\|\|)Delta\b/g, 'Δ'], [/(?:\\|\|)Theta\b/g, 'Θ'],
    [/(?:\\|\|)Lambda\b/g, 'Λ'], [/(?:\\|\|)Xi\b/g, 'Ξ'], [/(?:\\|\|)Pi\b/g, 'Π'],
    [/(?:\\|\|)Sigma\b/g, 'Σ'], [/(?:\\|\|)Phi\b/g, 'Φ'], [/(?:\\|\|)Psi\b/g, 'Ψ'], [/(?:\\|\|)Omega\b/g, 'Ω']
  ];
  for(const [rx, rep] of map) t = t.replace(rx, rep);
  t = t.replace(/(?:\\|\|)(?:left|right)\b/g, '');
  t = t.replace(/(?:\\|\|)frac\{([^{}]+)\}\{([^{}]+)\}/g, '($1)/($2)');
  t = t.replace(/(?:\\|\|)sqrt\{([^{}]+)\}/g, '√($1)');
  t = t.replace(/(?:\\|\|)(?:text|mathrm|mathbf|mathit|mathcal|operatorname|hat|bar|tilde|vec|dot)\{([^{}]+)\}/g, '$1');
  t = t.replace(/([_^])\{([^{}]{1,24})\}/g, '$1$2');
  const unwrap = (full, inner) => {
    const x = inner.trim();
    if(!x) return '';
    if(/^[\d,.]+$/.test(x)) return full;
    if(/^[A-Za-z_][A-Za-z0-9_.\[\]()]*$/.test(x)) return '`' + x + '`';
    return x;
  };
  t = t.replace(/\$\$([^$\n]{1,200})\$\$/g, unwrap);
  t = t.replace(/\$([^$\n]{1,120})\$/g, unwrap);
  return t;
}
const md = s => E(sanitizeTex(s).replace(/□/g, ' '))
  .replace(/&lt;sup&gt;([^&<]{1,24})&lt;\/sup&gt;/gi, '<sup>$1</sup>')
  .replace(/&lt;sub&gt;([^&<]{1,24})&lt;\/sub&gt;/gi, '<sub>$1</sub>')
  .replace(/\*\*([^*\n]+)\*\*/g, '<b>$1</b>')
  .replace(/(^|[^A-Za-z0-9_])_([^_\n]{1,40})_(?![A-Za-z0-9_])/g, '$1<i>$2</i>')
  .replace(/`([^`]+)`/g, '<code>$1</code>');
function _normInlineBullets(s){
  return String(s == null ? '' : s)
    .replace(/([.!?,:;。])\s+[-•]\s+/g, '$1\n- ')
    .replace(/\s+·\s+(?=(?:들어오는 값|내보내는 값|연결 함수|입력|출력|호출|주의)\s*[:：])/g, '\n- ');
}
function _mergeDanglingNumbers(lines){
  const out = [];
  for(let i = 0; i < lines.length; i++){
    const cur = lines[i].trim();
    if(!cur) continue;
    if(/^(?:[-*•]\s+)?\d+[.)]$/.test(cur) && i + 1 < lines.length){
      const num = cur.replace(/^[-*•]\s+/, '');
      const nxt = lines[i + 1].trim().replace(/^[-*•]\s+/, '');
      out.push(num + ' ' + nxt);
      i++;
    } else {
      out.push(cur);
    }
  }
  return out;
}
function _splitSentencesSafe(str){
  const s = String(str || '').trim();
  if(!s) return [];
  const out = []; let cur = '', inBt = false;
  const noSplitRx = /(?:^|\s)(?:\d+|et\s+al|Eq|Fig|Tab|Sec|Ref|vs|e\.g|i\.e|Dr|Mr|Ms|pp?|No|Vol)\.$/i;
  for(let i = 0; i < s.length; i++){
    const ch = s[i];
    if(ch === '`') inBt = !inBt;
    cur += ch;
    if(!inBt && (ch === '.' || ch === '!' || ch === '?' || ch === '。') && i + 1 < s.length && s[i + 1] === ' '){
      if(ch === '.' && noSplitRx.test(cur)) continue;
      const rest = s.slice(i + 2).trimStart();
      if(rest){ out.push(cur.trim()); cur = ''; while(i + 1 < s.length && s[i + 1] === ' ') i++; }
    }
  }
  if(cur.trim()) out.push(cur.trim());
  return out;
}
function mdBlock(s){
  const lines = _normInlineBullets(s).split('\n');
  let h = '', inUl = false, inOl = false;
  const closeLists = () => {
    if(inUl){ h += '</ul>'; inUl = false; }
    if(inOl){ h += '</ol>'; inOl = false; }
  };
  const isSep = ln => /^\|?\s*:?-{2,}:?\s*(?:\|\s*:?-{2,}:?\s*)+\|?$/.test(ln) || /^\|\s*:?-{2,}:?\s*\|$/.test(ln);
  const splitRow = ln => {
    let x = ln.trim();
    if(x.startsWith('|')) x = x.slice(1);
    if(x.endsWith('|')) x = x.slice(0, -1);
    return x.split('|').map(c => c.trim());
  };
  for(let i = 0; i < lines.length; i++){
    let t = lines[i].trim();
    if(!t){ closeLists(); continue; }
    if(/^\d+[.)]$/.test(t) && i + 1 < lines.length && lines[i + 1].trim()){
      t = t + ' ' + lines[i + 1].trim().replace(/^[-*•]\s+/, '');
      i++;
    }
    if(t.includes('|') && i + 1 < lines.length && isSep(lines[i + 1].trim())){
      closeLists();
      const hdrs = splitRow(t);
      h += '<div class="md-tbl-wrap"><table><thead><tr>' + hdrs.map(c => '<th>' + md(c) + '</th>').join('') + '</tr></thead><tbody>';
      i += 2;
      while(i < lines.length){
        const rt = lines[i].trim();
        if(!rt || !rt.includes('|')) { i--; break; }
        const cols = splitRow(rt);
        h += '<tr>' + hdrs.map((_, ci) => '<td>' + md(cols[ci] || '') + '</td>').join('') + '</tr>';
        i++;
      }
      h += '</tbody></table></div>';
      continue;
    }
    if(/^#{1,6}\s+/.test(t)){
      closeLists();
      h += '<div class="md-sec">' + md(t.replace(/^#{1,6}\s+/, '')) + '</div>';
    } else if(/^\*\*[^*]{2,80}\*\*$/.test(t) || /^(?:[1-9]\uFE0F?\u20E3|🧩|🔗|💡|🔎|🎯|🔢|🪜|🔄|🐍|🟨|🟦|⚙️|📐)\s+/.test(t) && t.startsWith('**')){
      closeLists();
      h += '<div class="md-sec">' + md(t) + '</div>';
    } else if(t.startsWith('- ') || t.startsWith('• ') || t.startsWith('* ')){
      if(inOl){ h += '</ol>'; inOl = false; }
      if(!inUl){ h += '<ul>'; inUl = true; }
      h += '<li>' + _splitSentencesSafe(t.slice(2)).map(md).join('<br>') + '</li>';
    } else if(/^\d+[.)]\s+/.test(t)){
      if(inUl){ h += '</ul>'; inUl = false; }
      if(!inOl){ h += '<ol>'; inOl = true; }
      h += '<li>' + _splitSentencesSafe(t.replace(/^\d+[.)]\s+/, '')).map(md).join('<br>') + '</li>';
    } else if(t.startsWith('> ')){
      closeLists();
      h += '<div class="hint">' + _splitSentencesSafe(t.slice(2)).map(md).join('<br>') + '</div>';
    } else {
      closeLists();
      h += '<p>' + _splitSentencesSafe(t).map(md).join('<br>') + '</p>';
    }
  }
  closeLists();
  return '<div class="md">' + (h || '<p></p>') + '</div>';
}
function _expandSummaryLines(txt){
  const raw = _normInlineBullets(txt).trim();
  if(!raw) return [];
  const rawLines = _mergeDanglingNumbers(raw.split(/\r?\n+/)).map(x => x.replace(/^[-*•]\s+/, '').trim()).filter(Boolean);
  const out = [];
  for(const ln of rawLines){
    for(const p of _splitSentencesSafe(ln)) out.push(p);
  }
  return out;
}
function fmtSummary(txt){
  const lines = _expandSummaryLines(txt);
  if(!lines.length) return '';
  if(lines.length <= 1) return '<div class="md"><p>' + md(lines[0]) + '</p></div>';
  return '<div class="md"><ul class="ov-sum">' + lines.map(ln => '<li>' + md(ln) + '</li>').join('') + '</ul></div>';
}
function fmtFlowStep(txt){
  const lines = _expandSummaryLines(txt);
  if(!lines.length) return '';
  if(lines.length === 1) return '<li>' + md(lines[0]) + '</li>';
  return '<li>' + md(lines[0]) + '<ul class="ov-sum">' + lines.slice(1).map(ln => '<li>' + md(ln) + '</li>').join('') + '</ul></li>';
}
const S = { tab:'code', file:0, line:1, unit:0, stmtA:1, info:null, hist:[], hi:-1, gHist:[], gHi:-1, vHist:[], vHi:-1, focus:false, ai:true, sideTab:'files', tutTab:'tutor',
  wikiTrCache:{}, wikiTrMode:{}, wikiViewMode:{},
  varSel:null, order:'down', filter:'', folded:new Set(), open:new Set(), closedDirs:new Set(), closedUnits:new Set(), foldedCards:new Set(), openWikiRefs:new Set(), graph:{view:null},
  selRange:null, activeStep:0, brief:null, briefKey:'', briefLoading:false, chatLoading:false, topCollapsed:false, sumCollapsed:false, linePeekOpen:false, level:'beginner',
  fontScope:'all', fonts:{l:13.5, c:13.5, r:13.5}, hideL:false, hideR:false,
  srvOk:false, llmCfg:{use_llm:false,base_url:'',model:'',has_key:false,extra_body:''}, prewarm:{active:false,done:0,total:0,cached:0},
  threads:{}, pins:{}, done:[], bookmarks:[], last:null };
const KIND_LABEL = {import:'불러오기',def:'정의',class:'클래스',assign:'대입',augassign:'누적',annassign:'타입대입',callstmt:'호출',expr:'식',docstring:'독스트링',return:'반환',raise:'예외',assert:'단언',if:'if',elif:'elif',else:'else',for:'for',while:'while',try:'try',except:'except',finally:'finally',with:'with',delete:'del',global:'global',pass:'pass',break:'break',continue:'continue',match:'match',comment:'주석',blank:'빈 줄',syntax:'구문',cont:'계속'};
const LANG_TAG = {py:'PY', js:'JS', ts:'TS', tsx:'TSX', c:'C', cpp:'C++', matlab:'MAT'};
const LANG_NM = {py:'Python', js:'JavaScript', ts:'TypeScript', tsx:'TSX', c:'C', cpp:'C++', matlab:'MATLAB'};
const UK = {m:'모듈 실행부', c:'클래스', f:'함수'};
const EFF = {file:'파일 I/O',net:'네트워크',proc:'외부 프로세스',gui:'GUI',out:'콘솔/로그 출력',thread:'스레드/병렬',sleep:'대기(sleep)',rand:'난수',glob:'전역 상태 변경'};
let store = null; try { store = window.localStorage; } catch(e) { store = null; }
const lsGet = (k, d) => { try { const v = store && store.getItem('ct:'+D.title+':'+k); return v == null ? d : JSON.parse(v); } catch(e){ return d; } };
const lsSet = (k, v) => { try { store && store.setItem('ct:'+D.title+':'+k, JSON.stringify(v)); } catch(e){} };
const gLsGet = (k, d) => { try { const v = store && store.getItem('ct_ui:'+k); return v == null ? d : JSON.parse(v); } catch(e){ return d; } };
const gLsSet = (k, v) => { try { store && store.setItem('ct_ui:'+k, JSON.stringify(v)); } catch(e){} };

function toast(m){ const t=$('#toast'); t.textContent=m; t.classList.add('show'); clearTimeout(toast._t); toast._t=setTimeout(()=>t.classList.remove('show'),1400); }
function copyText(txt){
  const done = () => toast('프롬프트를 복사했습니다');
  if(navigator.clipboard && window.isSecureContext){ navigator.clipboard.writeText(txt).then(done, () => fb()); } else fb();
  function fb(){ const ta=document.createElement('textarea'); ta.value=txt; document.body.appendChild(ta); ta.select(); try{document.execCommand('copy'); done();}catch(e){toast('복사 실패: 수동으로 선택하세요');} ta.remove(); }
}
const fileOf = u => FS[u.f];
const unitLabel = u => u.k === 'm' ? FS[u.f].path + ' (실행부)' : u.dn;
const shortFile = fid => { const p = (FS[fid] && FS[fid].path) || ''; return p.includes('/') ? p.split('/').pop() : p; };
const shortTxt = (s, n) => { s = String(s == null ? '' : s).trim(); return s.length > n ? s.slice(0, n - 1) + '…' : s; };
const stars = n => '●'.repeat(n) + '○'.repeat(5 - n);
const dcls = n => 'd' + Math.max(1, Math.min(5, n));
const palette = i => 'hsl(' + ((i * 67) % 360) + ',55%,' + (document.documentElement.classList.contains('light') ? '45%' : '62%') + ')';

/* ───────────── 코드 렌더링 ───────────── */
function lineHtml(segs){
  let o = '';
  for(const s of segs){
    const t = E(s[0]), cls = s[1] || '', k = s[2];
    if(k === 'c'){ const q = s[4]; o += '<span class="call'+(q==='g'?' g':'')+(cls?' '+cls:'')+'" data-c="'+s[3]+'" title="'+E(s[5])+' — Ctrl+클릭/더블클릭: 이동">'+t+'</span>'; }
    else if(k === 'r'){ o += '<span class="ref" data-c="'+s[3]+'" title="'+E(s[4])+' (함수를 호출하지 않고 넘겨주는 참조) — Ctrl+클릭: 이동">'+t+'</span>'; }
    else if(k === 'e'){ o += '<span class="ext '+cls+'" title="'+E(s[3])+'">'+t+'</span>'; }
    else if(k === 'v'){ o += '<span'+(cls?' class="'+cls+'"':'')+' data-v="'+E(s[3])+'">'+t+'</span>'; }
    else if(cls){ o += '<span class="'+cls+'">'+t+'</span>'; }
    else o += t;
  }
  return o || ' ';
}
let renderedFile = -1;
let codeRows = [], codeFolds = [], actRows = [], stmRows = [], selBlockRows = [], vhTokens = [], lastHid = null;
function renderCode(){
  const fd = fdata(S.file), f = FS[S.file];
  const aiLines = new Set();
  const stepMap = {};
  f.us.forEach(id => {
    const u = U[id];
    if(u.ai && u.ai.l) Object.keys(u.ai.l).forEach(k => aiLines.add(+k));
    if((u.k === 'f' || u.k === 'm') && u.stps) u.stps.forEach(st => { if(!stepMap[st.l1]) stepMap[st.l1] = {u:id, st}; });
  });
  const out = [];
  for(let i = 0; i < fd.L.length; i++){
    const ln = i + 1, inf = fd.I[i];
    let gt = '';
    if((inf.k === 'def' || inf.k === 'class') && inf.d !== undefined){ const du = U[inf.d]; if(du.e > du.l) gt = '<span class="fold" data-fold="'+du.id+'" title="접기/펼치기">▾</span>'; }
    else if(stepMap[ln]){ const sp = stepMap[ln]; gt = '<span class="sbadge" data-su="'+sp.u+'" data-step="'+sp.st.id+'" title="Step '+sp.st.id+': '+E(sp.st.t)+' (클릭해 블록 해설)">S'+sp.st.id+'</span>'; }
    else if(aiLines.has(ln)) gt = '<span class="aid" title="AI 해설 있음">●</span>';
    out.push('<div class="ln" data-l="'+ln+'"><span class="gt">'+gt+'</span><span class="nm">'+ln+'</span><span class="tx">'+lineHtml(fd.L[i])+'</span></div>');
  }
  const codeEl = $('#code');
  codeEl.innerHTML = out.join('');
  codeRows = Array.from(codeEl.children);
  codeFolds = $$('#code .fold');
  actRows = []; stmRows = []; selBlockRows = []; vhTokens = [];
  lastHid = new Uint8Array(codeRows.length + 2);
  renderedFile = S.file;
  S.folded = new Set();
}
function clearSelBlock(){ selBlockRows.forEach(e => e.classList.remove('sel-block')); selBlockRows = []; }
function applySelection(){
  clearSelBlock();
  $$('#code .sbadge.on').forEach(e => e.classList.remove('on'));
  if(S.selRange){
    const [a, b] = S.selRange;
    for(let i = a; i <= b; i++){ const r = rowOf(i); if(r){ r.classList.add('sel-block'); selBlockRows.push(r); } }
  }
  if(S.activeStep){
    const sb = $('#code .sbadge[data-su="'+S.unit+'"][data-step="'+S.activeStep+'"]');
    if(sb) sb.classList.add('on');
  }
}
function rowOf(l){ return codeRows[l - 1] || null; }
function applyVisibility(){
  const n = codeRows.length; if(!n) return;
  const hid = new Uint8Array(n + 2);
  if(S.focus){
    const u = U[S.unit];
    if(u && u.k !== 'm'){ const fd = fdata(S.file); let a = u.l; const inf = fd.I[u.l-1]; if(inf && inf.a) a = Math.min(a, inf.a);
      for(let i = 1; i <= n; i++) if(i < a || i > u.e) hid[i] = 1; }
  }
  S.folded.forEach(id => { const u = U[id]; for(let i = u.l + 1; i <= Math.min(u.e, n); i++) hid[i] = 1; });
  for(let i = 0; i < n; i++){
    const v = hid[i + 1];
    if(!lastHid || lastHid[i + 1] !== v) codeRows[i].classList.toggle('hid', !!v);
  }
  lastHid = hid;
  codeFolds.forEach(el => { const want = S.folded.has(+el.dataset.fold) ? '▸' : '▾'; if(el.textContent !== want) el.textContent = want; });
}
function applyVar(){
  vhTokens.forEach(e => e.classList.remove('vh')); vhTokens = [];
  if(!S.varSel) return;
  const u = U[S.unit]; if(!u) return;
  const lo = Math.max(1, u.k === 'm' ? 1 : u.l), hi = Math.min(codeRows.length, u.k === 'm' ? codeRows.length : u.e);
  for(let l = lo; l <= hi; l++){
    const r = codeRows[l - 1]; if(!r) continue;
    const vs = r.querySelectorAll('[data-v]');
    for(let j = 0; j < vs.length; j++){ if(vs[j].dataset.v === S.varSel){ vs[j].classList.add('vh'); vhTokens.push(vs[j]); } }
  }
}

/* ───────────── 이동/선택 ───────────── */
function gotoLine(file, line, opt){
  opt = opt || {};
  if(opt.push !== false){ S.hist = S.hist.slice(0, S.hi + 1); S.hist.push([S.file, S.line]); S.hi = S.hist.length - 1; }
  setTab('code');
  if(file !== S.file || renderedFile !== file){ S.file = file; renderCode(); renderSide(); }
  selectLine(line, opt);
  if(opt.push !== false){ S.hist.push([S.file, S.line]); S.hi = S.hist.length - 1; }
}
function gotoUnit(id){ const u = U[id]; if(!u) return; gotoLine(u.f, u.l); }
function histMove(d){
  const ni = S.hi + d; if(ni < 0 || ni >= S.hist.length) return;
  S.hi = ni; const [f, l] = S.hist[ni]; setTab('code');
  if(f !== S.file || renderedFile !== f){ S.file = f; renderCode(); renderSide(); }
  selectLine(l, {});
}
function selectLine(l, opt){
  opt = opt || {};
  const fd = fdata(S.file), n = fd.I.length; if(!n) return;
  l = Math.max(1, Math.min(n, l)); S.line = l;
  let inf = fd.I[l-1]; let st = inf, a = l;
  if(inf.k === 'cont'){ a = inf.a; st = fd.I[a-1]; }
  S.stmtA = a; S.info = st;
  const prevUnit = S.unit;
  const uid = st.d !== undefined ? st.d : (st.u !== undefined ? st.u : (inf.u !== undefined ? inf.u : FS[S.file].mu));
  S.unit = uid;
  if(uid !== prevUnit){
    if(!opt.keepRange){ S.selRange = null; S.activeStep = 0; }
    S.brief = null; S.briefKey = '';
  } else if(opt.clearRange){
    S.selRange = null; S.activeStep = 0; S.brief = null; S.briefKey = '';
  }
  actRows.forEach(e => e.classList.remove('act')); actRows = [];
  stmRows.forEach(e => e.classList.remove('stm')); stmRows = [];
  const z = st.z || l; for(let i = a; i <= z; i++){ const r = rowOf(i); if(r){ r.classList.add('stm'); stmRows.push(r); } }
  const r = rowOf(l); if(r){ r.classList.add('act'); actRows.push(r); if(!opt.noscroll) r.scrollIntoView({block:'nearest'}); }
  applySelection(); applyVisibility(); applyVar(); renderCrumb(); renderTutor(); renderSide(true);
  $('#lineInd').textContent = 'Line ' + l + ' / ' + n;
  recordLastStudy(uid, S.file, l, S.activeStep || 0);
}
let _lastTimer = null;
function recordLastStudy(uid, fileId, line, stepId){
  const u = U[uid]; if(!u || u.k === 'c') return;
  const obj = {unit_id: uid, file_id: fileId, line: line, step_id: stepId || 0};
  S.last = obj;
  clearTimeout(_lastTimer);
  _lastTimer = setTimeout(() => { saveStudyState({last: obj}); }, 600);
}
function selectRange(l1, l2, opt){
  opt = opt || {};
  const a = Math.min(l1, l2), b = Math.max(l1, l2);
  S.selRange = [a, b];
  S.activeStep = opt.stepId || 0;
  S.brief = null; S.briefKey = '';
  if(opt.unitId !== undefined){ S.unit = opt.unitId; }
  selectLine(a, {noscroll: !!opt.noscroll, keepRange: true});
}
function selectStep(uid, stepId){
  const u = U[uid]; if(!u) return;
  if(stepId === 0){
    S.selRange = null; S.activeStep = 0; S.brief = null; S.briefKey = '';
    if(S.file !== u.f || renderedFile !== u.f){ gotoLine(u.f, u.l, {push:false, clearRange:true}); }
    else { selectLine(u.l, {noscroll:false, clearRange:true}); }
    return;
  }
  const st = (u.stps || []).find(s => s.id === stepId);
  if(!st) return;
  if(S.file !== u.f || renderedFile !== u.f){ S.file = u.f; renderCode(); renderSide(); }
  selectRange(st.l1, st.l2, {stepId: st.id, unitId: uid, noscroll: false});
}
function stepStmt(d){
  const fd = fdata(S.file); let l = S.line;
  if(d > 0){ const inf = fd.I[l-1]; const st = inf.k === 'cont' ? fd.I[inf.a-1] : inf; l = (st.z || l) + 1; }
  else { const inf = fd.I[l-1]; const a = inf.k === 'cont' ? inf.a : l; l = a - 1; if(l >= 1 && fd.I[l-1].k === 'cont') l = fd.I[l-1].a; }
  while(l >= 1 && l <= fd.I.length){ const k = fd.I[l-1].k; if(k !== 'blank' && !(S.focus && !inFocus(l))) break; l += d; }
  selectLine(l);
}
function inFocus(l){ const u = U[S.unit]; return u && u.k !== 'm' && l >= u.l && l <= u.e; }
function stepUnit(d){
  const fu = FS[S.file].us.map(i => U[i]).filter(u => u.k === 'f');
  if(!fu.length) return;
  let idx = fu.findIndex(u => u.id === S.unit); if(idx < 0) idx = d > 0 ? -1 : fu.length;
  const nu = fu[Math.max(0, Math.min(fu.length - 1, idx + d))]; gotoLine(nu.f, nu.l);
}
function renderCrumb(){
  const u = U[S.unit], f = FS[S.file]; let h = '<b class="mono">' + E(f.path) + '</b>';
  const chain = []; let p = u; while(p && p.k !== 'm'){ chain.unshift(p); p = U[p.p]; }
  chain.forEach(c => { h += ' › <a data-gu="'+c.id+'">' + E(c.n) + '</a>'; });
  if(f.err) h += ' <span class="tag dead">구문 오류: 정적 해설 없음</span>';
  $('#crumb').innerHTML = h;
  $$('#crumb a').forEach(a => a.onclick = () => gotoUnit(+a.dataset.gu));
  if(S.selRange){
    const [a, b] = S.selRange;
    const stObj = S.activeStep && u && u.stps ? u.stps.find(s => s.id === S.activeStep) : null;
    const lbl = stObj ? ('Step ' + stObj.id + ': ' + stObj.t) : ('L' + a + '–' + b + ' (' + (b - a + 1) + '줄)');
    $('#selBar').innerHTML = '<span class="selpill">' + E(lbl) + ' <button data-clr-sel="1" style="padding:0 5px;font-size:.85em">전체 함수</button></span>';
    const clr = $('#selBar [data-clr-sel]'); if(clr) clr.onclick = () => selectStep(S.unit, 0);
  } else {
    $('#selBar').innerHTML = '';
  }
}

/* ───────────── 튜터 패널 ───────────── */
function aiBadge(ai){ return ai.st === 'ok' ? '<span class="badge b-ai ok" title="형식·언어·식별자 검증을 모두 통과한 LLM 문장. 그래도 참고용입니다.">AI · 검증 통과</span>' : '<span class="badge b-ai" title="일부 표현(존재하지 않는 식별자 등)을 제거했거나 일부 줄 설명을 버렸습니다.">AI · 일부 미검증</span>'; }
const stBadge = '<span class="badge b-st" title="소스 코드를 직접 분석해 계산한 내용입니다">정적 분석 · 확실</span>';
function chipsVars(list, cls){ return (list || []).map(v => '<span class="chip '+cls+(S.varSel===v?' on':'')+'" data-var="'+E(v)+'">'+E(v)+'</span>').join(''); }
function lineText(fd, l){ return (fd.L[l-1] || []).map(s => s[0]).join(''); }
function codeOfUnit(u, mark){
  const fd = fdata(u.f), o = [];
  for(let l = u.l; l <= Math.min(u.e, fd.L.length); l++) o.push((l === mark ? '>> ' : '   ') + l + ': ' + lineText(fd, l));
  return o.join('\n');
}
function activeRange(){
  const u = U[S.unit] || U[0];
  if(S.selRange) return S.selRange;
  return [u.l, u.e];
}
function promptFor(kind){
  const u = U[S.unit] || U[0], fd = fdata(S.file), inf = S.info || {};
  if(kind === 'line'){
    const t = lineText(fd, S.line).trim();
    return '다음 코드 줄의 역할과 데이터 흐름을 쉽게 설명해 주세요.\n파일: ' + FS[S.file].path + ':' + S.line + ' (' + u.dn + ')\n코드: ' + t + (inf.x ? '\n참고: ' + inf.x : '');
  }
  return '다음 함수의 전체 의도와 실행 흐름을 쉽게 설명해 주세요.\n파일: ' + FS[u.f].path + ':' + u.l + '-' + u.e + '\n대상: ' + (u.sig || u.dn) + '\n코드:\n' + codeOfUnit(u, S.line);
}
function localBrief(u, l1, l2){
  const steps = (u.stps || []).filter(s => !(s.l2 < l1 || s.l1 > l2));
  const exact = (u.stps || []).find(s => s.l1 === l1 && s.l2 === l2);
  const title = exact ? (u.dn + ' — Step ' + exact.id + ': ' + exact.t) : (l1 <= u.l && l2 >= u.e ? u.dn + ' — 전체 맥락 요약' : u.dn + ' — 선택 구간 L' + l1 + '–L' + l2);
  const intent = exact ? (exact.d + ' ' + exact.w) : (u.st && u.st.one ? u.st.one : u.dn + ' 구간의 논리를 수행합니다.');
  const flow = steps.length ? steps.map(s => '**Step ' + s.id + ' · ' + s.t + '** (`L' + s.l1 + '–L' + s.l2 + '`): ' + s.d) : ['`L' + l1 + '–L' + l2 + '` 구문을 순서대로 실행합니다.'];
  const df = (u.st && u.st.bul && u.st.bul.length) ? u.st.bul.slice(0, 2).join(' · ') : '함수 내부 지역 상태를 처리합니다.';
  const lg = (FS[u.f] && FS[u.f].lang) || 'py', lnm = LANG_NM[lg] || lg.toUpperCase();
  const lico = {py:'🐍', js:'🟨', ts:'🟦', tsx:'🟦', c:'⚙️', cpp:'⚙️', matlab:'📐'}[lg] || '🧩';
  return {
    ok:true, unit_id:u.id, range:[l1, l2], step_id:exact ? exact.id : 0, title, source:'static', model:'',
    intent, flow, data_flow:df, caution:u.rc ? '재귀 함수이므로 종료 조건을 먼저 확인하세요.' : '정적 분석 기반 맥락 해설입니다.',
    suggestions:[
      {mode:'trace', label:'💡 예시 값 대입해서 추적하기', q:'예시 값을 넣어서 실행 흐름 따라가 보기'},
      {mode:'why', label:'🧩 이 구간의 존재 이유(Why)와 맥락', q:'이 구간이 왜 필요하고 전체에서 무슨 역할을 해?'},
      {mode:'connect', label:'🔗 호출 함수·데이터 연결 흐름', q:'호출하는 함수와 앞뒤 흐름 연결해 보기'},
      {mode:'syntax', label:lico + ' 사용된 ' + lnm + ' 문법 쉽게 풀이', q:'이 구간에 쓰인 ' + lnm + ' 문법 풀어줘'}
    ],
    llm_note:''
  };
}
function localAnswer(u, l1, l2, q, mode){
  const b = localBrief(u, l1, l2);
  let txt = '**' + b.title + '**\n' + b.intent + '\n\n' + b.flow.map(x => '- ' + x).join('\n');
  if(mode === 'connect'){
    const ca = (u.ca || []).map(x => '- 호출자: `' + unitLabel(U[x[0]]) + '`').join('\n') || '- 호출자 없음(진입점)';
    const co = (u.co || []).map(x => '- 호출 대상: `' + unitLabel(U[x[0]]) + '`').join('\n') || '- 내부 호출 없음';
    txt = '**🔗 호출 연결**\n' + ca + '\n' + co;
  }
  txt += '\n\n> *오프라인 HTML 상태입니다. `--serve` 로 실행하면 대화·예시 추적·내부망 LLM 연결이 모두 동작합니다.*';
  return {
    user_msg:{id:'u'+Date.now(), role:'user', range:[l1, l2], q, mode, ts:''},
    assistant_msg:{id:'a'+Date.now(), role:'assistant', range:[l1, l2], title:'💬 맥락 답변', text:txt, source:'static', model:'', suggestions:b.suggestions.slice(0,3), ts:''}
  };
}
async function apiPost(url, body){
  const r = await fetch(url, {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify(body)});
  if(!r.ok) throw new Error('HTTP ' + r.status);
  return await r.json();
}
function loadBrief(force){
  const u = U[S.unit]; if(!u) return;
  const [l1, l2] = activeRange();
  const key = u.id + ':' + l1 + ':' + l2 + ':' + S.level + ':' + (S.llmCfg.use_llm ? 1 : 0);
  if(!force && S.briefKey === key && S.brief) return;
  S.briefKey = key;
  if(!S.srvOk){
    S.brief = localBrief(u, l1, l2);
    S.briefLoading = false;
    return;
  }
  S.briefLoading = true;
  renderChatTutor(true);
  apiPost('/api/brief', {unit_id:u.id, file_id:S.file, l1, l2, level:S.level, force:!!force})
    .then(res => {
      if(S.briefKey !== key) return;
      S.brief = res; S.briefLoading = false;
      renderChatTutor(false);
    })
    .catch(() => {
      if(S.briefKey !== key) return;
      S.brief = localBrief(u, l1, l2); S.briefLoading = false;
      renderChatTutor(false);
    });
}
async function sendQuestion(q, mode){
  q = (q || '').trim(); if(!q || S.chatLoading) return;
  const u = U[S.unit]; if(!u) return;
  const [l1, l2] = activeRange();
  S.chatLoading = true;
  const th = S.threads[String(u.id)] = S.threads[String(u.id)] || [];
  const tempU = {id:'tmp_'+Date.now(), role:'user', range:[l1, l2], q, mode:mode||'chat', ts:''};
  th.push(tempU);
  renderChatTutor(false, true);
  try{
    if(S.srvOk){
      const res = await apiPost('/api/chat', {unit_id:u.id, file_id:S.file, l1, l2, question:q, mode:mode||'chat', level:S.level, var_name:(S.tutTab === 'var' && S.varSel) ? S.varSel : ''});
      if(res.ok && res.thread){ S.threads[String(u.id)] = res.thread; }
    } else {
      const loc = localAnswer(u, l1, l2, q, mode||'chat');
      th[th.length - 1] = loc.user_msg;
      th.push(loc.assistant_msg);
    }
  } catch(e){
    th.push({id:'err_'+Date.now(), role:'assistant', range:[l1, l2], title:'⚠ 오류', text:'응답 중 오류가 발생했습니다: ' + String(e), source:'static', suggestions:[], ts:''});
  } finally {
    S.chatLoading = false;
    renderChatTutor(false, true);
  }
}
async function togglePinMsg(msg){
  const u = U[S.unit]; if(!u || !msg) return;
  const k = String(u.id);
  const plist = S.pins[k] = S.pins[k] || [];
  if(S.srvOk){
    const res = await apiPost('/api/pin', {unit_id:u.id, action:'add', pin_id:'p_'+msg.id, title:msg.title, text:msg.text, range:msg.range});
    if(res.ok) S.pins[k] = res.pins;
  } else {
    plist.push({id:'p_'+msg.id, title:msg.title || '고정 노트', text:msg.text, range:msg.range || []});
  }
  toast('상단 노트에 고정했습니다');
  renderChatTutor(false);
}
async function removePin(pinId){
  const u = U[S.unit]; if(!u) return;
  const k = String(u.id);
  if(S.srvOk){
    const res = await apiPost('/api/pin', {unit_id:u.id, action:'remove', pin_id:pinId});
    if(res.ok) S.pins[k] = res.pins;
  } else {
    S.pins[k] = (S.pins[k] || []).filter(p => p.id !== pinId);
  }
  renderChatTutor(false);
}
const clampPx = px => Math.max(10.5, Math.min(24, Math.round(px * 2) / 2));
function syncFontUI(){
  const r = document.documentElement.style;
  r.setProperty('--fs-l', S.fonts.l + 'px');
  r.setProperty('--fs-c', S.fonts.c + 'px');
  r.setProperty('--fs-r', S.fonts.r + 'px');
  r.setProperty('--fs', S.fonts.c + 'px');
  lsSet('fonts', S.fonts);
  const b = $('#bFontRst'), sc = S.fontScope || 'all';
  if(b){
    if(sc === 'all'){
      const same = S.fonts.l === S.fonts.c && S.fonts.c === S.fonts.r;
      b.textContent = same ? (Math.round(S.fonts.c / 13.5 * 100) + '%') : '초기화';
    } else {
      b.textContent = Math.round(S.fonts[sc] / 13.5 * 100) + '%';
    }
  }
}
function changeFont(delta, reset){
  const sc = S.fontScope || 'all';
  const keys = sc === 'all' ? ['l', 'c', 'r'] : [sc];
  if(reset){
    keys.forEach(k => { S.fonts[k] = 13.5; });
  } else if(sc === 'all'){
    const same = S.fonts.l === S.fonts.c && S.fonts.c === S.fonts.r;
    const base = S.fonts.c;
    keys.forEach(k => { S.fonts[k] = clampPx((same ? base : S.fonts[k]) + delta); });
  } else {
    S.fonts[sc] = clampPx(S.fonts[sc] + delta);
  }
  syncFontUI();
}
function applyPanels(){
  const side = $('#side'), tut = $('#tutor');
  if(side) side.classList.toggle('col', !!S.hideL);
  if(tut) tut.classList.toggle('col', !!S.hideR);
  const bL = $('#bTogL'), bR = $('#bTogR'), sL = $('#bSpL'), sR = $('#bSpR');
  if(bL) bL.classList.toggle('on', !!S.hideL);
  if(bR) bR.classList.toggle('on', !!S.hideR);
  if(sL) sL.textContent = S.hideL ? '›' : '‹';
  if(sR) sR.textContent = S.hideR ? '‹' : '›';
  lsSet('hideL', !!S.hideL);
  lsSet('hideR', !!S.hideR);
  if(S.tab === 'graph') setTimeout(renderGraph, 240);
}
function togglePanel(which, force){
  if(which === 'l') S.hideL = force === undefined ? !S.hideL : !!force;
  else S.hideR = force === undefined ? !S.hideR : !!force;
  applyPanels();
}
function initTooltip(){
  const tip = $('#tip'); if(!tip) return;
  let curEl = null, tipShown = false;
  const hideTip = () => { if(!curEl && !tipShown) return; curEl = null; tipShown = false; tip.style.display = 'none'; };
  const placeTip = (mx, my) => {
    const tw = tip.offsetWidth, th = tip.offsetHeight;
    let x = mx - Math.min(tw / 2, Math.max(16, tw - 24));
    x = Math.max(8, Math.min(window.innerWidth - tw - 8, x));
    let y = my - th - 14;
    if(y < 6){
      y = Math.max(6, my + 18);
      if(my >= 6 && my < 46){
        // 상단 헤더 위 호버 시에도 커서를 가리지 않도록 옆/아래 여백 확보
        const rightX = mx + 16, leftX = mx - tw - 16;
        if(rightX + tw < window.innerWidth - 8){ x = rightX; y = my + 16; }
        else if(leftX >= 8){ x = leftX; y = my + 16; }
      }
    }
    tip.style.left = x + 'px';
    tip.style.top = y + 'px';
  };
  const claimTip = target => {
    const el0 = target && target.nodeType === 1 ? target : (target && target.parentElement);
    if(!el0 || !el0.closest) return null;
    const hit = el0.closest('[title],[data-tip],.gn');
    if(!hit) return null;
    let n = hit;
    while(n && n !== document){
      if(n.nodeType === 1){
        if(n.hasAttribute && n.hasAttribute('title')){
          const tv = n.getAttribute('title');
          if(tv) n.setAttribute('data-tip', tv);
          n.removeAttribute('title');
        }
        if(n.classList && n.classList.contains('gn')){
          const st = Array.from(n.children || []).find(ch => ch.tagName && ch.tagName.toLowerCase() === 'title');
          if(st){
            if(st.textContent) n.setAttribute('data-tip', st.textContent);
            st.remove();
          }
        }
      }
      n = n.parentNode;
    }
    return el0.closest('[data-tip]');
  };
  document.addEventListener('mouseover', e => {
    const el = claimTip(e.target);
    if(!el){ hideTip(); return; }
    const txt = el.getAttribute('data-tip');
    if(!txt){ hideTip(); return; }
    curEl = el;
    tipShown = true;
    tip.textContent = txt;
    tip.style.display = 'block';
    placeTip(e.clientX, e.clientY);
  });
  document.addEventListener('mousemove', e => {
    if(tipShown && curEl) placeTip(e.clientX, e.clientY);
  });
  document.addEventListener('mouseout', e => {
    if(curEl && (!e.relatedTarget || !curEl.contains(e.relatedTarget))) hideTip();
  });
  document.addEventListener('mousedown', hideTip);
  document.addEventListener('wheel', hideTip, {passive:true});
  document.addEventListener('scroll', hideTip, true);
}
async function saveStudyState(patch){
  if(patch.done) lsSet('done', patch.done);
  if(patch.bookmarks) lsSet('bookmarks', patch.bookmarks);
  if(patch.last) lsSet('last', patch.last);
  if(!S.srvOk) return;
  try{
    const res = await apiPost('/api/study_state', patch);
    if(res && res.ok){
      if(res.done) S.done = res.done;
      if(res.bookmarks) S.bookmarks = res.bookmarks;
      if(res.last) S.last = res.last;
    }
  } catch(e){}
}
function toggleBookmark(uid){
  const s = new Set(S.bookmarks || []);
  if(s.has(uid)) s.delete(uid); else s.add(uid);
  S.bookmarks = [...s];
  saveStudyState({bookmarks: S.bookmarks});
  renderChatTutor(true); renderSide(true);
  toast(s.has(uid) ? '복습 북마크에 추가했습니다' : '북마크를 해제했습니다');
}
function toggleDone(uid){
  const s = new Set(S.done || []);
  if(s.has(uid)) s.delete(uid); else s.add(uid);
  S.done = [...s];
  saveStudyState({done: S.done});
  renderChatTutor(true); renderSide(true);
  toast(s.has(uid) ? '학습 완료로 표시했습니다' : '학습 완료 표시를 해제했습니다');
}
function exprUsesVar(expr, v){
  if(!expr || !v) return false;
  const esc = v.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return new RegExp('(^|[^A-Za-z0-9_])' + esc + '([^A-Za-z0-9_]|$)').test(expr);
}
function splitCallArgs(raw, fnName){
  if(!raw || !fnName) return [];
  const esc = fnName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  const m = new RegExp('(?:^|[^A-Za-z0-9_])' + esc + '\\s*\\(').exec(raw);
  if(!m) return [];
  let i = m.index + m[0].length, dep = 1, cur = '', q = '';
  const args = [];
  for(; i < raw.length && dep > 0; i++){
    const ch = raw[i];
    if(q){ cur += ch; if(ch === q && raw[i - 1] !== '\\') q = ''; continue; }
    if(ch === '"' || ch === "'"){ q = ch; cur += ch; continue; }
    if(ch === '(' || ch === '[' || ch === '{') dep++;
    else if(ch === ')' || ch === ']' || ch === '}'){ dep--; if(dep === 0){ if(cur.trim()) args.push(cur.trim()); break; } }
    else if(ch === ',' && dep === 1){ args.push(cur.trim()); cur = ''; continue; }
    cur += ch;
  }
  return args;
}
function pushVarSnap(uid, file, line, varSel){
  const sn = {unit: uid !== undefined ? uid : S.unit, file: file !== undefined ? file : S.file, line: line !== undefined ? line : S.line, varSel: varSel !== undefined ? varSel : S.varSel};
  if(!S.vHist.length){ S.vHist = [sn]; S.vHi = 0; return; }
  const cur = S.vHist[S.vHi];
  if(cur && cur.unit === sn.unit && cur.file === sn.file && cur.line === sn.line && cur.varSel === sn.varSel) return;
  S.vHist = S.vHist.slice(0, S.vHi + 1);
  S.vHist.push(sn);
  S.vHi = S.vHist.length - 1;
}
function varHistMove(delta){
  const ni = S.vHi + delta;
  if(ni < 0 || ni >= S.vHist.length) return;
  S.vHi = ni;
  const st = S.vHist[ni];
  S.varSel = st.varSel || null;
  S.tutTab = 'var';
  if(st.file !== S.file || st.line !== S.line) gotoLine(st.file, st.line, {push: false});
  else { applyVar(); renderTutor(); }
}
function hopTrace(uid, varName, line){
  const tu = U[uid]; if(!tu) return;
  if(!S.vHist.length) pushVarSnap();
  S.varSel = varName || null;
  if(S.varSel) S.tutTab = 'var';
  gotoLine(tu.f, line || tu.l);
  pushVarSnap(tu.id, tu.f, line || tu.l, S.varSel);
  renderTutor();
}
function renderVarLineage(u, varName){
  if(!u || !varName) return '';
  const v = (u.va || []).find(x => x[0] === varName);
  const vk = 'var:' + u.id + ':' + varName, vFold = S.foldedCards.has(vk);
  if(!v){
    return '<div class="card var-card"><h4>🔎 변수 흐름 추적: <code>' + E(varName) + '</code><span class="sp"></span><button data-clr-var="1" class="tbtn">추적 해제</button></h4><div class="small muted">이 함수 범위 안에 기록된 변수가 아닙니다.</div></div>';
  }
  const [nm, kind, typ, defs, uses] = v;
  const fd = fdata(u.f);
  const paIdx = (u.pa || []).filter((p, idx) => !(idx === 0 && (p.n === 'self' || p.n === 'cls'))).findIndex(p => p.n === nm);
  const isParam = kind === 'param' || paIdx >= 0;
  const kLabel = {param:'입력 매개변수', global:'전역 변수', attr:'객체 속성', local:'지역 변수', import:'가져온 이름', def:'내부 정의'}[kind] || kind;

  let h = '<div class="card var-card"><h4 class="card-tog" data-fc="' + E(vk) + '" style="' + (vFold ? 'margin-bottom:0' : '') + '">' + (vFold ? '▸ ' : '▾ ') + '🔎 변수 흐름 추적: <code>' + E(nm) + '</code> <span class="tag">' + E(kLabel) + (typ ? ' · ' + E(typ) : '') + '</span><span class="sp"></span><button data-clr-var="1" class="tbtn">추적 종료</button></h4>';
  if(vFold) return h + '</div>';

  // ① 어디서 입력/생성되었나 (출처)
  h += '<div class="vt-sec"><div class="vt-lbl">① 어디서 들어왔나 (입력·출처)</div>';
  if(isParam){
    const paObj = (u.pa || []).find(p => p.n === nm);
    h += '<div class="small"><b>' + E(u.dn) + '</b> 의 <b>' + (paIdx >= 0 ? (paIdx + 1) + '번째 ' : '') + '입력 인자</b>' + (paObj && paObj.d ? ' (기본값 <code>' + E(paObj.d) + '</code>)' : '') + '로 넘겨받습니다.</div>';
    const callers = (u.ca || []).slice(0, 5);
    if(callers.length){
      callers.forEach(([cid, ek, lns]) => {
        const cu = U[cid]; if(!cu) return;
        const cfd = fdata(cu.f);
        (lns || [cu.l]).slice(0, 2).forEach(ln => {
          const raw = lineText(cfd, ln);
          const args = splitCallArgs(raw, u.n);
          const argExpr = (paIdx >= 0 && args[paIdx]) ? args[paIdx] : '';
          let hopBtn = '';
          if(argExpr && cu.va){
            const pv = cu.va.find(x => exprUsesVar(argExpr, x[0])) || cu.va.find(x => argExpr.includes(x[0]));
            if(pv) hopBtn = ' <button class="tbtn" data-trace-hop="' + cid + ':' + ln + ':' + E(pv[0]) + '">◀ 상위 변수 `' + E(pv[0]) + '` 추적</button>';
          }
          h += '<div class="vt-item"><div class="small muted">호출자 <span class="chip" data-gu="' + cid + '">' + E(unitLabel(cu)) + '</span>' + (argExpr ? ' 가 <code>' + E(argExpr) + '</code> 전달' : '') + hopBtn + '</div>' + codeSnippetHtml(cu.f, ln) + '</div>';
        });
      });
    } else {
      h += '<div class="small muted">상위 호출자 없음 (진입점 함수이거나 외부에서 직접 입력값을 받아 실행)</div>';
    }
  } else if(kind === 'global' || nm.startsWith('self.') || nm.startsWith('this.')){
    h += '<div class="small">함수 밖에서도 공유되는 <b>전역·객체 상태 변수</b>입니다.</div>';
  } else if(defs && defs.length){
    h += '<div class="small">이 함수 내부 <b>L' + defs[0][0] + '</b> 에서 처음 계산되어 만들어졌습니다.</div>';
  } else {
    h += '<div class="small muted">상위/전역 스코프에서 참조됩니다.</div>';
  }
  h += '</div>';

  // ② 어떻게 생성되고 값이 바뀌나 (대입/갱신)
  const assigns = (defs || []).filter(d => !(String(d[1] || '').startsWith('(매개변수)')));
  h += '<div class="vt-sec"><div class="vt-lbl">② 값 생성·갱신 (' + assigns.length + '곳)</div>';
  if(!assigns.length){
    h += '<div class="small muted">' + (isParam ? '입력받은 값 그대로 읽기 전용으로 사용합니다 (함수 내부 재대입 없음).' : '이 함수 안에서 직접 대입되는 코드가 없습니다.') + '</div>';
  } else {
    assigns.slice(0, 8).forEach(([dln, expr]) => {
      const inf = fd.I[dln - 1] || {};
      const viaCalls = (inf.c || []).filter(c => c[1] >= 0).map(c => '<span class="chip" data-gu="' + c[1] + '">← ' + E(c[0]) + ' 결과</span>').join(' ');
      h += '<div class="vt-item">' + codeSnippetHtml(u.f, dln) + (viaCalls ? '<div class="small" style="margin-top:2px">' + viaCalls + '</div>' : '') + '</div>';
    });
    if(assigns.length > 8) h += '<div class="small muted">… 외 ' + (assigns.length - 8) + '곳 더 있음</div>';
  }
  h += '</div>';

  // ③ 어디에서 쓰이고 어떤 함수로 넘어가나 (사용·전달·반환)
  const useLines = [...new Set(uses || [])].sort((a, b) => a - b);
  h += '<div class="vt-sec"><div class="vt-lbl">③ 사용처 · 함수 전달 (' + useLines.length + '곳)</div>';
  if(!useLines.length){
    h += '<div class="small muted">이 스코프 안에서 이후에 다시 읽히는 곳이 없습니다.</div>';
  } else {
    useLines.slice(0, 10).forEach(uln => {
      const inf = fd.I[uln - 1] || {};
      const raw = lineText(fd, uln);
      let role = '값 참조';
      if(inf.k === 'if' || inf.k === 'elif') role = '조건 판정';
      else if(inf.k === 'for' || inf.k === 'while') role = '반복 제어';
      else if(inf.k === 'return') role = '반환(Return)';
      else if(inf.w && inf.w.length && !inf.w.includes(nm)) role = '다른 변수 계산';
      const hops = [];
      (inf.c || []).forEach(c => {
        const [lab, cid] = c;
        if(cid < 0 || !U[cid]) return;
        const cu = U[cid], fnBase = lab.replace(/^@/, '').replace(/\(\)$/, '');
        const args = splitCallArgs(raw, fnBase);
        const aIdx = args.findIndex(a => exprUsesVar(a, nm));
        const cParams = (cu.pa || []).filter((p, idx) => !(idx === 0 && (p.n === 'self' || p.n === 'cls')));
        if(aIdx >= 0 && cParams[aIdx]){
          const cp = cParams[aIdx].n;
          role = '하위 함수 전달';
          hops.push('<button class="tbtn" data-trace-hop="' + cid + ':' + cu.l + ':' + E(cp) + '">▶ ' + E(cu.n) + ' 의 인자 `' + E(cp) + '` 로 따라가기</button>');
        }
      });
      const derived = (inf.w || []).filter(w => w !== nm).slice(0, 2).map(w => '<span class="chip w" data-var="' + E(w) + '">→ `' + E(w) + '` 에 담김</span>').join('');
      h += '<div class="vt-item"><div class="small muted"><span class="tag">' + role + '</span> ' + derived + hops.join(' ') + '</div>' + codeSnippetHtml(u.f, uln) + '</div>';
    });
    if(useLines.length > 10) h += '<div class="small muted">… 외 ' + (useLines.length - 10) + '곳 더 있음</div>';
  }
  const retNames = String(u.ret || '').split(',').map(x => x.trim()).filter(Boolean);
  const isRet = retNames.includes(nm) || (u.rets || []).some(r => exprUsesVar(r, nm));
  if(isRet){
    h += '<div class="vt-item" style="margin-top:6px"><span class="tag ent">📤 호출자에게 반환/출력됨</span>';
    if(retNames.includes(nm) && (u.ca || []).length){
      const [cid, _k, lns] = u.ca[0];
      const cu = U[cid];
      if(cu){
        const cfd = fdata(cu.f), ln = (lns && lns[0]) || cu.l;
        h += ' <button class="tbtn" data-trace-hop="' + cid + ':' + ln + ':' + '">◀ 받는 쪽(' + E(cu.n) + ' L' + ln + ') 보기</button>';
      }
    }
    h += '</div>';
  }
  h += '</div>';

  // ④ 프로젝트 내 다른 함수에서의 쓰임 (특히 global / 공유 이름)
  const others = [];
  U.forEach(ou => {
    if(ou.id === u.id || ou.k === 'c' || !ou.va) return;
    const ov = ou.va.find(x => x[0] === nm);
    if(ov && (kind === 'global' || ov[1] === 'global' || nm.startsWith('self.') || ou.f !== u.f)){
      others.push({ou, ov});
    }
  });
  if(others.length){
    h += '<div class="vt-sec"><div class="vt-lbl">④ 다른 함수에서도 같은 변수(`' + E(nm) + '`) 쓰임 (' + others.length + '곳)</div><div class="small">';
    others.slice(0, 8).forEach(({ou, ov}) => {
      const wr = (ov[3] || []).length, rd = (ov[4] || []).length;
      const ln = (ov[3] && ov[3][0] && ov[3][0][0]) || (ov[4] && ov[4][0]) || ou.l;
      h += '<button class="chip" data-trace-hop="' + ou.id + ':' + ln + ':' + E(nm) + '" title="클릭해서 해당 함수에서 계속 추적">' + E(unitLabel(ou)) + ' <span class="muted">(대입' + wr + '/사용' + rd + ')</span></button>';
    });
    h += '</div></div>';
  }
  return h + '</div>';
}
function wireTraceControls(root){
  $$('[data-trace-hop]', root).forEach(b => b.onclick = ev => {
    ev.stopPropagation();
    const parts = b.dataset.traceHop.split(':');
    const uid = +parts[0], ln = +parts[1], vn = parts.slice(2).join(':');
    hopTrace(uid, vn, ln);
  });
  $$('[data-go-loc]', root).forEach(e => e.onclick = ev => { ev.stopPropagation(); const [f, l] = e.dataset.goLoc.split(':').map(Number); gotoLine(f, l); });
}
function renderVarPanel(u, th){
  const [l1, l2] = activeRange();
  const topEl = $('#tutTop');
  topEl.style.display = 'none';
  let h = '<div class="card" style="padding:8px 10px"><div style="display:flex;align-items:center;gap:6px;flex-wrap:wrap"><b class="mono" style="color:var(--ac)">' + E(unitLabel(u)) + '</b><span class="small muted">변수를 클릭하면 흐름을 추적합니다</span><span class="sp"></span><button class="tbtn" id="vBack" title="이전 변수 추적"' + (S.vHi <= 0 ? ' disabled' : '') + '>◀</button><button class="tbtn" id="vFwd" title="다음 변수 추적"' + (S.vHi < 0 || S.vHi >= S.vHist.length - 1 ? ' disabled' : '') + '>▶</button>' + (S.varSel ? '<button class="tbtn" data-clr-var="1">선택 해제</button>' : '') + '</div>';
  const paNames = (u.pa || []).map(p => p.n).filter(n => n !== 'self' && n !== 'cls');
  const retNames = String(u.ret || '').split(',').map(x => x.trim()).filter(Boolean);
  const allVars = (u.va || []).map(x => x[0]).filter(n => !paNames.includes(n) && !retNames.includes(n));
  if(paNames.length){
    h += '<div class="small muted" style="margin-top:6px">입력 인자: ' + paNames.slice(0, 16).map(n => '<span class="chip v' + (S.varSel === n ? ' on' : '') + '" data-var="' + E(n) + '">' + E(n) + '</span>').join('') + '</div>';
  }
  if(retNames.length){
    h += '<div class="small muted" style="margin-top:4px">출력 변수: ' + retNames.slice(0, 16).map(n => '<span class="chip w' + (S.varSel === n ? ' on' : '') + '" data-var="' + E(n) + '">' + E(n) + '</span>').join('') + '</div>';
  }
  if(allVars.length){
    h += '<div class="small muted" style="margin-top:4px">내부·전역 변수: ' + allVars.slice(0, 18).map(n => '<span class="chip' + (S.varSel === n ? ' on' : '') + '" data-var="' + E(n) + '">' + E(n) + '</span>').join('') + (allVars.length > 18 ? ' <span class="muted">+' + (allVars.length - 18) + '</span>' : '') + '</div>';
  }
  h += '</div>';
  if(S.varSel){
    h += renderVarLineage(u, S.varSel);
    h += '<div class="sugg-wrap"><button class="sugg-btn" data-vq="1">💡 `' + E(S.varSel) + '` 값이 어디서 와서 어떻게 변하나요?</button><button class="sugg-btn" data-vq="2">🔗 `' + E(S.varSel) + '` 가 다른 함수에서 어떤 역할을 하나요?</button></div>';
  } else {
    h += '<div class="card muted small">위 목록이나 왼쪽 코드(1번 줄 입·출력 포함)에서 변수를 클릭하면 <b>어디서 입력되어 → 어떻게 가공되고 → 어디로 전달되는지</b> 흐름을 추적합니다.</div>';
  }
  th.forEach((m, idx) => {
    if(m.role === 'user'){
      const nxt = th[idx + 1];
      const uk = (nxt && nxt.role === 'assistant') ? ('msg:' + nxt.id) : ('u:' + m.id);
      const uFold = S.foldedCards.has(uk);
      h += '<div class="msg-user cl" data-fc="' + E(uk) + '"><span class="small muted">' + (uFold ? '▸ ' : '▾ ') + (m.range ? 'L' + m.range[0] + '–' + m.range[1] + ' · ' : '') + '</span>🙋 ' + E(m.q) + '</div>';
    } else {
      const mk = 'msg:' + m.id, mFold = S.foldedCards.has(mk);
      const badge = m.source === 'llm' ? '<span class="badge b-ai ok">AI · ' + E(m.model || 'LLM') + '</span>' : '<span class="badge b-st">정적 맥락</span>';
      h += '<div class="msg-asst"><div class="card-tog" data-fc="' + E(mk) + '" style="display:flex;align-items:center;gap:6px;' + (mFold ? 'margin-bottom:0' : 'margin-bottom:4px') + '"><b style="color:var(--ac)">' + (mFold ? '▸ ' : '▾ ') + E(m.title || '🤖 튜터 답변') + '</b>' + (m.ts ? '<span class="small muted">' + E(m.ts) + '</span>' : '') + '<span class="sp"></span>' + badge + '</div>';
      if(!mFold){ h += mdBlock(m.text || ''); }
      h += '</div>';
    }
  });
  if(S.chatLoading) h += '<div class="msg-asst"><span class="muted">🤖 답변을 작성하고 있습니다…</span></div>';
  const thEl = $('#tutThread');
  thEl.innerHTML = h;
  $$('[data-fc]', thEl).forEach(e => e.onclick = () => { const k = e.dataset.fc; if(S.foldedCards.has(k)) S.foldedCards.delete(k); else S.foldedCards.add(k); renderChatTutor(true); });
  $$('[data-gu]', thEl).forEach(e => e.onclick = ev => { ev.stopPropagation(); gotoUnit(+e.dataset.gu); });
  $$('[data-var]', thEl).forEach(e => e.onclick = ev => { ev.stopPropagation(); if(!S.vHist.length) pushVarSnap(); S.varSel = S.varSel === e.dataset.var ? null : e.dataset.var; pushVarSnap(); applyVar(); renderChatTutor(true); });
  const vb = $('#vBack', thEl); if(vb) vb.onclick = ev => { ev.stopPropagation(); varHistMove(-1); };
  const vf = $('#vFwd', thEl); if(vf) vf.onclick = ev => { ev.stopPropagation(); varHistMove(1); };
  const clr = $('[data-clr-var]', thEl); if(clr) clr.onclick = ev => { ev.stopPropagation(); S.varSel = null; applyVar(); renderChatTutor(true); };
  $$('[data-vq]', thEl).forEach(b => b.onclick = () => {
    const q = b.dataset.vq === '1'
      ? ('변수 `' + S.varSel + '` 값이 어디서 입력되어 어떻게 변하는지 단계별로 설명해 줘')
      : ('변수 `' + S.varSel + '` 가 이 함수와 연결된 다른 함수에서 어떤 역할을 하나요?');
    sendQuestion(q, 'chat');
  });
  wireTraceControls(thEl);
  $('#chatTarget').textContent = S.varSel ? ('변수: ' + S.varSel) : ('함수: ' + u.n + ' (L' + l1 + '–' + l2 + ')');
}
function renderChatTutor(skipBriefFetch, scrollBottom){
  const u = U[S.unit]; if(!u) return;
  const th = S.threads[String(u.id)] || [];
  if(S.tutTab === 'var'){
    renderVarPanel(u, th);
    if(scrollBottom){ const thEl = $('#tutThread'); thEl.scrollTop = thEl.scrollHeight; }
    return;
  }
  $('#tutTop').style.display = 'block';
  if(!skipBriefFetch) loadBrief(false);
  const [l1, l2] = activeRange();
  const isWhole = (l1 <= u.line || l1 <= u.l) && l2 >= u.e;
  const stps = u.stps || [];
  const pins = S.pins[String(u.id)] || [];
  const isBmk = (S.bookmarks || []).includes(u.id);
  const isDn = (S.done || []).includes(u.id);

  // 1) 상단 고정 기준 카드
  let topH = '<div style="display:flex;align-items:center;gap:4px;flex-wrap:wrap"><b class="mono" style="color:var(--ac)">' + E(unitLabel(u)) + '</b><span class="tag">' + (u.e - u.l + 1) + '줄</span><span class="sp"></span>';
  topH += '<button class="tbtn' + (isBmk ? ' bmk' : '') + '" data-bmk-tog="1" title="복습용 북마크">' + (isBmk ? '⭐ 북마크됨' : '☆ 북마크') + '</button>';
  topH += '<button class="tbtn' + (isDn ? ' dn' : '') + '" data-done-tog="1" title="학습 완료 표시">' + (isDn ? '✓ 완료됨' : '✓ 완료') + '</button>';
  topH += '<button class="tbtn" data-top-tog="1">' + (S.topCollapsed ? '펼치기 ▾' : '접기 ▴') + '</button></div>';
  if(!S.topCollapsed){
    const sumTxt = (u.ai && S.ai && u.ai.s) || (u.st && u.st.one) || '';
    if(sumTxt){
      topH += '<div class="top-sum' + (S.sumCollapsed ? ' fold' : '') + '" data-sum-tog="1" title="클릭해서 한 줄 요약 접기/펼치기"><span class="small muted">' + (S.sumCollapsed ? '▸' : '▾') + '</span><span class="small muted top-sum-txt" style="flex:1;min-width:0">' + md(sumTxt) + '</span></div>';
    }
    if(stps.length){
      const stFold = S.foldedCards.has('top:steps');
      const stInfo = S.activeStep ? ('Step ' + S.activeStep) : (stps.length + '단계');
      topH += '<div class="top-box"><div class="top-box-lbl card-tog" data-fc="top:steps" style="' + (stFold ? 'margin-bottom:0' : '') + '"><span>' + (stFold ? '▸ ' : '▾ ') + '🔢 논리 단계별 보기</span><span class="sp"></span><span class="tag">' + E(stInfo) + '</span></div>';
      if(!stFold){
        topH += '<div class="step-pills"><button class="spill' + (!S.selRange ? ' on' : '') + '" data-step-pick="0">전체</button>';
        stps.forEach(s => { topH += '<button class="spill' + (S.activeStep === s.id ? ' on' : '') + '" data-step-pick="' + s.id + '" title="' + E(s.d) + '">S' + s.id + ': ' + E(s.t) + '</button>'; });
        topH += '</div>';
      }
      topH += '</div>';
    }
    const sortE = arr => (arr || []).slice().sort((a, b) => (a[1] === 'call' ? 0 : 1) - (b[1] === 'call' ? 0 : 1));
    const upE = sortE(u.ca), dnE = sortE(u.co);
    if(upE.length || dnE.length){
      const brFold = S.foldedCards.has('top:bridge');
      topH += '<div class="top-box"><div class="top-box-lbl card-tog" data-fc="top:bridge" style="' + (brFold ? 'margin-bottom:0' : '') + '"><span>' + (brFold ? '▸ ' : '▾ ') + '🔗 전후 호출 흐름</span><span class="sp"></span><span class="tag">▲' + upE.length + ' · ▼' + dnE.length + '</span></div>';
      if(!brFold){
        topH += '<div class="call-bridge">';
        upE.slice(0, 2).forEach(([cid, k, lns]) => {
          const cu = U[cid]; if(!cu) return;
          const cf = cu.f !== u.f ? '<span class="bf">' + E(shortFile(cu.f)) + ':</span>' : '';
          topH += '<button class="bchip up" data-gu="' + cid + '" title="상위 호출자: ' + E(FS[cu.f].path) + ' L' + (lns[0] || cu.l) + '">◀ ' + cf + E(cu.n) + '</button>';
        });
        if(upE.length > 2) topH += '<button class="bchip" data-go-flow="1" title="호출자 전체 보기">+' + (upE.length - 2) + '</button>';
        if(upE.length) topH += '<span class="muted">→</span>';
        topH += '<span class="bchip cur">★ ' + E(u.n) + '</span>';
        if(dnE.length) topH += '<span class="muted">→</span>';
        dnE.slice(0, 2).forEach(([cid, k, lns]) => {
          const cu = U[cid]; if(!cu) return;
          const cf = cu.f !== u.f ? ' <span class="bf">(' + E(shortFile(cu.f)) + ')</span>' : '';
          topH += '<button class="bchip dn" data-gu="' + cid + '" title="호출 대상: ' + E(FS[cu.f].path) + ':' + cu.l + '">' + E(cu.n) + cf + ' ▶</button>';
        });
        if(dnE.length > 2) topH += '<button class="bchip" data-go-flow="1" title="실행 흐름·구조 탭에서 전체 보기">+' + (dnE.length - 2) + '</button>';
        topH += '</div>';
      }
      topH += '</div>';
    }
    const inf = S.info || {}, qOpen = !!S.linePeekOpen;
    const varCnt = (inf.r ? inf.r.length : 0) + (inf.w ? inf.w.length : 0);
    const kLab = KIND_LABEL[inf.k] || inf.k || '';
    const rawSum = (inf.t && inf.t !== kLab) ? inf.t : (inf.x || '');
    const qlSummary = shortTxt(rawSum, 46);
    topH += '<div class="quick-line"><div class="quick-head" data-qline-tog="1"><span>' + (qOpen ? '▾' : '▸') + ' 🔍 L' + S.line + '</span>' + (kLab ? '<span class="tag">' + E(kLab) + '</span>' : '') + '<span class="muted" style="flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + md(qlSummary) + '</span>' + (varCnt ? '<span class="tag">변수 ' + varCnt + '</span>' : '') + '</div>';
    if(qOpen){
      topH += '<div class="quick-body">';
      if(inf.t) topH += '<div><b>' + E(inf.t) + '</b></div>';
      if(inf.x) topH += '<div class="small" style="margin:2px 0">' + md(inf.x) + '</div>';
      if(inf.h) topH += '<div class="hint" style="margin:3px 0">' + md(inf.h) + '</div>';
      if(inf.r && inf.r.length) topH += '<div class="small muted" style="margin-top:3px">읽음: ' + chipsVars(inf.r, 'v') + '</div>';
      if(inf.w && inf.w.length) topH += '<div class="small muted" style="margin-top:2px">씀: ' + chipsVars(inf.w, 'w') + '</div>';
      if(inf.m && inf.m.length) topH += '<div class="small muted" style="margin-top:2px">변경 가능: ' + chipsVars(inf.m, 'm') + '</div>';
      if(inf.c && inf.c.length){
        topH += '<div class="small muted" style="margin-top:3px">호출: ' + inf.c.slice(0, 5).map(c => '<span class="chip" ' + (c[1] >= 0 ? 'data-gu="' + c[1] + '"' : '') + ' title="' + E(c[3] || '') + '">' + E(c[0]) + '</span>').join('') + '</div>';
      }
      topH += '</div>';
    }
    topH += '</div>';
    if(pins.length){
      pins.forEach(p => {
        const pk = 'pin:' + p.id, pFold = S.foldedCards.has(pk);
        topH += '<div class="pin-item"><div class="pin-head card-tog" data-fc="' + E(pk) + '" style="' + (pFold ? 'margin-bottom:0' : '') + '"><span>' + (pFold ? '▸ ' : '▾ ') + '📌 ' + E(p.title) + '</span>' + (p.range && p.range.length ? '<span class="tag">L' + p.range[0] + '–' + p.range[1] + '</span>' : '') + (p.ts ? '<span class="small muted">' + E(p.ts) + '</span>' : '') + '<span class="sp"></span><button data-unpin="' + E(p.id) + '" style="padding:0 5px;font-size:.8em">×</button></div>' + (pFold ? '' : mdBlock(p.text)) + '</div>';
      });
    }
  }
  const topEl = $('#tutTop');
  topEl.innerHTML = topH;
  const tog = $('[data-top-tog]', topEl); if(tog) tog.onclick = () => { S.topCollapsed = !S.topCollapsed; renderChatTutor(true); };
  const stog = $('[data-sum-tog]', topEl); if(stog) stog.onclick = () => { S.sumCollapsed = !S.sumCollapsed; renderChatTutor(true); };
  const bmk = $('[data-bmk-tog]', topEl); if(bmk) bmk.onclick = () => toggleBookmark(u.id);
  const dnb = $('[data-done-tog]', topEl); if(dnb) dnb.onclick = () => toggleDone(u.id);
  $$('[data-step-pick]', topEl).forEach(b => b.onclick = () => selectStep(u.id, +b.dataset.stepPick));
  $$('[data-gu]', topEl).forEach(b => b.onclick = ev => { ev.stopPropagation(); gotoUnit(+b.dataset.gu); });
  $$('[data-gl]', topEl).forEach(b => b.onclick = ev => { ev.stopPropagation(); gotoLine(U[S.unit].f, +b.dataset.gl); });
  $$('[data-go-flow]', topEl).forEach(b => b.onclick = () => { S.tutTab = 'flow'; renderTutor(); });
  const qlt = $('[data-qline-tog]', topEl); if(qlt) qlt.onclick = () => { S.linePeekOpen = !S.linePeekOpen; renderChatTutor(true); };
  $$('[data-var]', topEl).forEach(b => b.onclick = () => { S.varSel = b.dataset.var; S.tutTab = 'var'; applyVar(); renderTutor(); });
  $$('[data-unpin]', topEl).forEach(b => b.onclick = ev => { ev.stopPropagation(); removePin(b.dataset.unpin); });
  $$('[data-fc]', topEl).forEach(e => e.onclick = () => { const k = e.dataset.fc; if(S.foldedCards.has(k)) S.foldedCards.delete(k); else S.foldedCards.add(k); renderChatTutor(true); });

  const refMap = {};
  const renderWikiRefs = (refs, pfx) => {
    if(!refs || !refs.length) return '';
    const outerKey = 'refs:' + pfx;
    const outerOpen = S.openWikiRefs.has(outerKey);
    return '<details class="wiki-refs" data-ref-outer="' + E(outerKey) + '"' + (outerOpen ? ' open' : '') + '><summary>📚 참고 논문/Wiki 근거 (' + refs.length + '건)</summary>' +
      refs.map((r, ri) => {
        const rk = pfx + ':' + ri;
        refMap[rk] = r;
        const hasLink = !!(r.code_link && r.code_link.trim());
        const hasWiki = !!(r.wiki_summary && r.wiki_summary.trim());
        const defMode = hasLink ? 'link' : 'orig';
        const viewMode = S.wikiViewMode[rk] || defMode;
        const isLinkView = (viewMode === 'link' && hasLink);
        const isWikiView = (viewMode === 'wiki' && hasWiki);
        const isOrigView = (!isLinkView && !isWikiView);
        const isKo = (isOrigView && S.wikiTrMode[rk] === 'ko');
        const koTxt = S.wikiTrCache[rk];
        const showTxt = isLinkView ? r.code_link : (isWikiView ? r.wiki_summary : ((isKo && koTxt) ? koTxt : (r.snippet || '')));
        const rFold = S.foldedCards.has('ref:' + rk);
        const locLbl = isWikiView ? 'Wiki 요약' : (r.loc || '');
        const locCls = (isLinkView || (isWikiView && r.wiki_is_llm)) ? 'tag ent' : 'tag';
        const linkOrigBtn = hasLink
          ? '<button class="tbtn" data-wv-ref="' + E(rk) + '" title="코드-논문 연결 해설 / 원문 발췌 전환">' + (isLinkView ? '원문 발췌' : '연결 해설') + '</button>'
          : '';
        const wikiBtn = hasWiki
          ? '<button class="tbtn" data-ww-ref="' + E(rk) + '" title="논문 전체 Wiki 요약 보기"' + (isWikiView ? ' style="border-color:var(--ac);color:var(--ac)"' : '') + '>' + (isWikiView ? 'Wiki 닫기' : 'Wiki 요약') + '</button>'
          : '';
        const trLbl = isKo ? '원문' : '한글';
        const trDis = !isOrigView ? ' disabled title="원문 발췌 보기에서 활성화됩니다" style="opacity:.42;cursor:not-allowed"' : ' title="원문 / 한글 번역 전환"';
        const bodyCls = isLinkView ? 'wiki-ref-body' : 'wiki-ref-body muted';
        return '<div class="wiki-ref-item"><div class="wiki-ref-hdr">' +
          '<span class="wiki-ref-doc" data-open-wdoc="' + E(r.doc_id || '') + '" title="클릭해서 원본 파일 열기">📄 ' + E(r.doc) + '</span>' +
          '<span class="' + locCls + '">' + E(locLbl) + '</span><span class="sp"></span>' +
          linkOrigBtn + wikiBtn +
          '<button class="tbtn" data-tr-ref="' + E(rk) + '"' + trDis + '>' + trLbl + '</button>' +
          '<button class="tbtn" data-fc="ref:' + E(rk) + '">' + (rFold ? '펼치기 ▾' : '접기 ▴') + '</button>' +
          '</div>' +
          (rFold ? '' : '<div class="' + bodyCls + '">' + mdBlock(showTxt) + '</div>') +
          '</div>';
      }).join('') +
      '</details>';
  };
  // 2) 중앙 해설 + 꼬리질문 스레드
  let midH = '';
  if(th.length){
    midH += '<div class="thread-bar"><span class="small muted">카드 ' + (1 + Math.ceil(th.length / 2)) + '개</span><span class="sp"></span><button data-fold-all="old">이전 모두 접기</button><button data-fold-all="expand">모두 펴기</button></div>';
  }
  const bKey = 'brief:' + S.briefKey;
  if(S.briefLoading && !S.brief){
    midH += '<div class="card brief-card"><div class="muted">🤖 선택한 코드 구간의 맥락을 분석하고 있습니다…</div></div>';
  } else if(S.brief){
    const b = S.brief, bFold = S.foldedCards.has(bKey);
    const badge = b.source === 'llm' ? '<span class="badge b-ai ok">AI 맥락 · ' + E(b.model || 'LLM') + '</span>' : '<span class="badge b-st">정적 맥락 튜터</span>';
    midH += '<div class="card brief-card"><h4 class="card-tog" data-fc="' + E(bKey) + '" style="' + (bFold ? 'margin-bottom:0' : '') + '">' + (bFold ? '▸ ' : '▾ ') + E(b.title) + '<span class="sp"></span>' + badge + '</h4>';
    if(!bFold){
      if(S.briefLoading) midH += '<div class="small muted" style="margin-bottom:6px">⏳ AI 맥락 해설을 불러오는 중…</div>';
      if(b.llm_note) midH += '<div class="small" style="color:var(--warn);margin-bottom:6px">⚠ ' + E(b.llm_note) + '</div>';
      midH += '<div class="brief-sec"><b>🎯 핵심 의도</b>' + fmtSummary(b.intent || '') + '</div>';
      if(b.flow && b.flow.length){
        const flowHtml = b.flow.map(x => fmtFlowStep(x)).join('');
        midH += '<div class="brief-sec"><b>🔢 논리 흐름</b><div class="md"><ul>' + flowHtml + '</ul></div></div>';
      }
      if(b.data_flow) midH += '<div class="brief-sec"><b>🔄 데이터 연결</b>' + fmtSummary(b.data_flow) + '</div>';
      if(b.caution) midH += '<div class="brief-sec"><div class="hint"><b>⚠ 포인트</b>' + fmtSummary(b.caution) + '</div></div>';
      if(b.refs && b.refs.length) midH += renderWikiRefs(b.refs, bKey);
    }
    midH += '</div>';
    if(b.suggestions && b.suggestions.length && !th.length && !bFold){
      midH += '<div class="small muted" style="margin:2px 0 4px">👇 처음이라면 클릭만 해서 바로 이어 보세요</div><div class="sugg-wrap">';
      b.suggestions.forEach((sg, idx) => { midH += '<button class="sugg-btn" data-sg-brief="' + idx + '">' + E(sg.label) + '</button>'; });
      midH += '</div>';
    }
  }

  th.forEach((m, idx) => {
    if(m.role === 'user'){
      const nxt = th[idx + 1];
      const uk = (nxt && nxt.role === 'assistant') ? ('msg:' + nxt.id) : ('u:' + m.id);
      const uFold = S.foldedCards.has(uk);
      midH += '<div class="msg-user cl" data-fc="' + E(uk) + '" title="클릭해서 아래 답변 접기/펼치기"><span class="small muted">' + (uFold ? '▸ ' : '▾ ') + (m.range ? 'L' + m.range[0] + '–' + m.range[1] + ' · ' : '') + '</span>🙋 ' + E(m.q) + '</div>';
    } else {
      const mk = 'msg:' + m.id, mFold = S.foldedCards.has(mk);
      const badge = m.source === 'llm' ? '<span class="badge b-ai ok">AI · ' + E(m.model || 'LLM') + '</span>' : '<span class="badge b-st">정적 맥락</span>';
      midH += '<div class="msg-asst"><div class="card-tog" data-fc="' + E(mk) + '" style="display:flex;align-items:center;gap:6px;' + (mFold ? 'margin-bottom:0' : 'margin-bottom:4px') + '"><b style="color:var(--ac)">' + (mFold ? '▸ ' : '▾ ') + E(m.title || '🤖 튜터 답변') + '</b>' + (m.ts ? '<span class="small muted">' + E(m.ts) + '</span>' : '') + '<span class="sp"></span>' + badge + '</div>';
      if(!mFold){
        midH += mdBlock(m.text || '');
        if(m.refs && m.refs.length) midH += renderWikiRefs(m.refs, 'msg:' + m.id);
        midH += '<div class="msg-actions"><button data-pin-idx="' + idx + '">📌 상단 노트에 고정</button><button data-copy-idx="' + idx + '">📋 내용 복사</button><button data-del-idx="' + idx + '" title="이 질문/답변 카드 삭제">🗑 삭제</button></div>';
      }
      midH += '</div>';
      if(idx === th.length - 1 && m.suggestions && m.suggestions.length && !S.chatLoading && !mFold){
        midH += '<div class="sugg-wrap">';
        m.suggestions.forEach((sg, si) => { midH += '<button class="sugg-btn" data-sg-msg="' + idx + ':' + si + '">' + E(sg.label) + '</button>'; });
        midH += '</div>';
      }
    }
  });
  if(S.chatLoading) midH += '<div class="msg-asst"><span class="muted">🤖 답변을 작성하고 있습니다…</span></div>';

  const thEl = $('#tutThread');
  const prevScroll = thEl.scrollTop;
  thEl.innerHTML = midH;
  if(scrollBottom) thEl.scrollTop = thEl.scrollHeight;
  else thEl.scrollTop = prevScroll;

  $$('[data-fc]', thEl).forEach(e => e.onclick = () => { const k = e.dataset.fc; if(S.foldedCards.has(k)) S.foldedCards.delete(k); else S.foldedCards.add(k); renderChatTutor(true); });
  $$('[data-ref-outer]', thEl).forEach(d => d.ontoggle = () => { const k = d.dataset.refOuter; if(d.open) S.openWikiRefs.add(k); else S.openWikiRefs.delete(k); });
  $$('[data-open-wdoc]', thEl).forEach(el => el.onclick = async ev => {
    ev.stopPropagation();
    const did = el.dataset.openWdoc;
    if(!did) return;
    try {
      const res = await apiPost('/api/wiki/open', {doc_id: did});
      if(res && res.ok) toast('원본 파일 열기: ' + (res.path || did));
      else toast('열기 실패: ' + ((res && res.error) || '알 수 없는 오류'));
    } catch(e) { toast('원본 파일 열기 실패: ' + e.message); }
  });
  $$('[data-wv-ref]', thEl).forEach(b => b.onclick = ev => {
    ev.stopPropagation();
    const rk = b.dataset.wvRef;
    const r = refMap[rk];
    if(!r) return;
    const hasLink = !!(r.code_link && r.code_link.trim());
    const cur = S.wikiViewMode[rk] || (hasLink ? 'link' : 'orig');
    S.wikiViewMode[rk] = (cur === 'link') ? 'orig' : 'link';
    renderChatTutor(true);
  });
  $$('[data-ww-ref]', thEl).forEach(b => b.onclick = ev => {
    ev.stopPropagation();
    const rk = b.dataset.wwRef;
    const r = refMap[rk];
    if(!r) return;
    const hasLink = !!(r.code_link && r.code_link.trim());
    const cur = S.wikiViewMode[rk] || (hasLink ? 'link' : 'orig');
    S.wikiViewMode[rk] = (cur === 'wiki') ? (hasLink ? 'link' : 'orig') : 'wiki';
    renderChatTutor(true);
  });
  $$('[data-tr-ref]', thEl).forEach(b => b.onclick = async ev => {
    ev.stopPropagation();
    const rk = b.dataset.trRef;
    const r = refMap[rk];
    if(!r) return;
    const cur = S.wikiTrMode[rk] || 'orig';
    if(cur === 'ko'){ S.wikiTrMode[rk] = 'orig'; renderChatTutor(true); return; }
    if(S.wikiTrCache[rk]){ S.wikiTrMode[rk] = 'ko'; renderChatTutor(true); return; }
    b.disabled = true; b.textContent = '번역 중...';
    try {
      const res = await apiPost('/api/wiki/translate', {text: r.snippet || ''});
      if(res && res.ok && res.ko){
        S.wikiTrCache[rk] = res.ko;
        S.wikiTrMode[rk] = 'ko';
      } else {
        toast('번역 실패: ' + ((res && res.error) || 'LLM 연결을 확인하세요'));
      }
    } catch(e) { toast('번역 오류: ' + e.message); }
    renderChatTutor(true);
  });
  $$('[data-fold-all]', thEl).forEach(b => b.onclick = () => {
    if(b.dataset.foldAll === 'expand'){
      S.foldedCards.clear();
    } else {
      if(S.brief) S.foldedCards.add(bKey);
      let lastAsstIdx = -1;
      for(let i = th.length - 1; i >= 0; i--){ if(th[i].role === 'assistant'){ lastAsstIdx = i; break; } }
      th.forEach((m, i) => { if(m.role === 'assistant' && i !== lastAsstIdx) S.foldedCards.add('msg:' + m.id); });
    }
    renderChatTutor(true);
  });

  $$('[data-sg-brief]', thEl).forEach(b => b.onclick = () => {
    const sg = S.brief && S.brief.suggestions && S.brief.suggestions[+b.dataset.sgBrief];
    if(sg) sendQuestion(sg.q, sg.mode);
  });
  $$('[data-sg-msg]', thEl).forEach(b => b.onclick = () => {
    const [mi, si] = b.dataset.sgMsg.split(':').map(Number);
    const sg = th[mi] && th[mi].suggestions && th[mi].suggestions[si];
    if(sg) sendQuestion(sg.q, sg.mode);
  });
  $$('[data-pin-idx]', thEl).forEach(b => b.onclick = () => togglePinMsg(th[+b.dataset.pinIdx]));
  $$('[data-copy-idx]', thEl).forEach(b => b.onclick = () => { const m = th[+b.dataset.copyIdx]; if(m) copyText(m.text || ''); });
  $$('[data-del-idx]', thEl).forEach(b => b.onclick = async () => {
    const idx = +b.dataset.delIdx, m = th[idx];
    if(!m) return;
    if(S.srvOk){
      try{
        const res = await apiPost('/api/delete_msg', {unit_id: u.id, msg_id: m.id});
        if(res && res.ok){ S.threads[u.id] = res.thread || []; renderChatTutor(true); toast('카드를 삭제했습니다'); return; }
      } catch(e){ toast('삭제 실패: ' + e.message); return; }
    }
    const arr = (S.threads[u.id] || []).slice();
    if(idx > 0 && arr[idx - 1] && arr[idx - 1].role === 'user') arr.splice(idx - 1, 2);
    else arr.splice(idx, 1);
    S.threads[u.id] = arr;
    renderChatTutor(true);
    toast('카드를 삭제했습니다');
  });
  $$('[data-gu]', thEl).forEach(e => e.onclick = ev => { ev.stopPropagation(); gotoUnit(+e.dataset.gu); });
  $$('[data-var]', thEl).forEach(e => e.onclick = ev => { ev.stopPropagation(); S.varSel = e.dataset.var; S.linePeekOpen = true; applyVar(); renderChatTutor(true); });
  const thClr = $('[data-clr-var]', thEl); if(thClr) thClr.onclick = ev => { ev.stopPropagation(); S.varSel = null; applyVar(); renderChatTutor(true); };
  wireTraceControls(thEl);

  // 3) 하단 질문 대상 칩 갱신
  const stObj = S.activeStep && stps ? stps.find(s => s.id === S.activeStep) : null;
  $('#chatTarget').textContent = stObj ? ('대상: Step ' + stObj.id + ' (L' + l1 + '–' + l2 + ')') : (S.selRange ? ('대상: 선택 구간 L' + l1 + '–' + l2) : ('대상: ' + u.n + ' 전체'));
}
function renderTutor(){
  if(S.tutTab !== 'tutor' && S.tutTab !== 'var' && S.tutTab !== 'flow') S.tutTab = 'tutor';
  $$('.tuttabs button').forEach(b => b.classList.toggle('on', b.dataset.tt === S.tutTab));
  const isChat = (S.tutTab === 'tutor' || S.tutTab === 'var');
  $('#tutChatWrap').style.display = isChat ? 'flex' : 'none';
  $('#tutc').style.display = isChat ? 'none' : 'block';
  if(isChat){
    renderChatTutor(S.tutTab === 'var', false);
    return;
  }
  const box = $('#tutc');
  const navBar = '<div style="display:flex;align-items:center;gap:6px;margin-bottom:8px"><button class="tbtn" id="fBack" title="이전 위치 (Alt+←)"' + (S.hi <= 0 ? ' disabled' : '') + '>◀ 이전</button><button class="tbtn" id="fFwd" title="다음 위치 (Alt+→)"' + (S.hi < 0 || S.hi >= S.hist.length - 1 ? ' disabled' : '') + '>다음 ▶</button><span class="sp"></span><span class="small muted">' + E(unitLabel(U[S.unit])) + '</span></div>';
  box.innerHTML = navBar + tutFlow(U[S.unit]);
  wireTutor(box);
}
function codeSnippetHtml(fid, lineNum){
  const fd = fdata(fid), raw = (lineText(fd, lineNum) || '').trim();
  if(!raw) return '';
  return '<span class="step-code" data-go-loc="' + fid + ':' + lineNum + '" title="클릭해 해당 위치로 이동"><span class="muted">' + E(shortFile(fid)) + ':L' + lineNum + '</span>  ' + E(shortTxt(raw, 72)) + '</span>';
}
function findEntryPath(targetId){
  const sortE = arr => (arr || []).slice().sort((a, b) => (a[1] === 'call' ? 0 : 1) - (b[1] === 'call' ? 0 : 1));
  const nextStep = new Map(), visited = new Set([targetId]);
  const q = [[targetId, 0]];
  let startId = targetId, foundEn = !!(U[targetId] && U[targetId].en), bestDepth = 0;
  while(q.length && visited.size < 350){
    const [cur, dep] = q.shift(), cu = U[cur];
    if(!cu) continue;
    if(cur !== targetId && cu.en){ startId = cur; foundEn = true; break; }
    const callers = sortE(cu.ca);
    if(cur !== targetId && !callers.length && !foundEn && dep > bestDepth){ startId = cur; bestDepth = dep; }
    if(dep >= 8) continue;
    for(const [cid, k, lns] of callers){
      if(!visited.has(cid)){
        visited.add(cid);
        nextStep.set(cid, {to:cur, kind:k, lines:lns || []});
        q.push([cid, dep + 1]);
      }
    }
  }
  const path = [];
  let cur = startId, guard = 0;
  while(cur !== undefined && guard++ < 15){
    const st = nextStep.get(cur);
    path.push({id:cur, edge:st || null});
    if(cur === targetId || !st) break;
    cur = st.to;
  }
  return path.length ? path : [{id:targetId, edge:null}];
}
function tutFlow(u){
  if(!u) return '';
  const sortE = arr => (arr || []).slice().sort((a, b) => (a[1] === 'call' ? 0 : 1) - (b[1] === 'call' ? 0 : 1));
  const flg = FS[u.f] && FS[u.f].lang ? (LANG_NM[FS[u.f].lang] || FS[u.f].lang.toUpperCase()) : 'Python';

  let h = '';
  // Card 1: 시작점 -> 현재 함수 실행 경로 노선도
  const path = findEntryPath(u.id);
  h += '<div class="card"><h4>🚀 시작점 → 현재 함수 실행 경로<span class="sp"></span><span class="tag">' + E(flg) + '</span></h4>';
  h += '<div class="flow-route">';
  path.forEach((step, idx) => {
    const su = U[step.id], isCur = step.id === u.id;
    const one = (su.ai && S.ai && su.ai.s) || (su.st && su.st.one) || '';
    h += '<div class="flow-node' + (isCur ? ' cur' : '') + '" data-gu="' + su.id + '"><div style="display:flex;align-items:center;gap:5px;flex-wrap:wrap">' + (isCur ? '<span class="tag ent">★ 현재</span>' : (su.en ? '<span class="tag ent">진입점</span>' : '<span class="tag">' + (idx + 1) + '단계</span>')) + '<b class="mono">' + E(unitLabel(su)) + '</b><span class="small muted">' + E(shortFile(su.f)) + ':' + su.l + '</span></div>';
    if(one) h += '<div class="small muted" style="margin-top:2px">' + E(shortTxt(one, 76)) + '</div>';
    h += '</div>';
    if(step.edge){
      const nxt = U[step.edge.to], ln = (step.edge.lines && step.edge.lines[0]) || su.l;
      const xfile = nxt && nxt.f !== su.f;
      h += '<div class="flow-edge"><div style="min-width:0;flex:1"><div class="small muted">▼ ' + (step.edge.kind === 'ref' ? '참조 전달' : step.edge.kind === 'guess' ? '호출 추정' : '호출') + (xfile ? ' <span class="tag">다른 파일: ' + E(shortFile(su.f)) + ' → ' + E(shortFile(nxt.f)) + '</span>' : '') + '</div>' + codeSnippetHtml(su.f, ln) + '</div></div>';
    }
  });
  const dnTop = sortE(u.co).slice(0, 4);
  if(dnTop.length){
    h += '<div class="flow-edge"><div style="min-width:0;flex:1"><div class="small muted">▼ 다음 하위 호출 (' + (u.co || []).length + '개 중 ' + dnTop.length + '개)</div>';
    dnTop.forEach(([cid, k, lns]) => {
      const cu = U[cid]; if(!cu) return;
      const ln = lns && lns[0];
      h += '<div style="margin-top:3px"><span class="chip' + (k === 'guess' ? ' g' : '') + '" data-gu="' + cid + '">' + E(cu.dn) + (cu.f !== u.f ? ' (' + E(shortFile(cu.f)) + ')' : '') + '</span>' + (ln ? codeSnippetHtml(u.f, ln) : '') + '</div>';
    });
    h += '</div></div>';
  }
  h += '</div></div>';

  // Card 2: 호출 맥락 코드 미리보기 (호출자 & 피호출자)
  const upAll = sortE(u.ca), dnAll = sortE(u.co);
  const kCtx = 'flow:ctx:' + u.id, ctxFold = S.foldedCards.has(kCtx);
  h += '<div class="card"><h4 class="card-tog" data-fc="' + kCtx + '" style="' + (ctxFold ? 'margin-bottom:0' : '') + '">' + (ctxFold ? '▸ ' : '▾ ') + '📞 호출 맥락 코드 미리보기<span class="sp"></span><span class="tag">▲ ' + upAll.length + ' · ▼ ' + dnAll.length + '</span></h4>';
  if(!ctxFold){
    h += '<div class="small muted" style="margin:4px 0 2px"><b>▲ 이 함수를 부르는 곳 (' + upAll.length + ')</b></div>';
    if(!upAll.length) h += '<div class="small muted">직접 호출하는 상위 함수 없음 (진입점 또는 콜백 후보)</div>';
    upAll.slice(0, 12).forEach(([cid, k, lns]) => {
      const cu = U[cid]; if(!cu) return;
      const xfile = cu.f !== u.f;
      h += '<div class="ctx-item"><div><span class="chip' + (k === 'guess' ? ' g' : '') + '" data-gu="' + cid + '">' + E(unitLabel(cu)) + '</span>' + (xfile ? ' <span class="tag">' + E(shortFile(cu.f)) + '</span>' : '') + ' <span class="small muted">' + (k === 'ref' ? '참조' : k === 'guess' ? '추정' : '호출') + '</span></div>';
      const co = (cu.ai && S.ai && cu.ai.s) || (cu.st && cu.st.one) || '';
      if(co) h += '<div class="small muted">' + E(shortTxt(co, 72)) + '</div>';
      (lns || []).slice(0, 2).forEach(ln => { h += codeSnippetHtml(cu.f, ln); });
      h += '</div>';
    });
    h += '<div class="small muted" style="margin:8px 0 2px"><b>▼ 이 함수가 부르는 하위 함수 (' + dnAll.length + ')</b></div>';
    if(!dnAll.length) h += '<div class="small muted">프로젝트 내부 다른 함수 호출 없음</div>';
    dnAll.slice(0, 15).forEach(([cid, k, lns]) => {
      const cu = U[cid]; if(!cu) return;
      const xfile = cu.f !== u.f;
      h += '<div class="ctx-item"><div><span class="chip' + (k === 'guess' ? ' g' : '') + '" data-gu="' + cid + '">' + E(unitLabel(cu)) + '</span>' + (xfile ? ' <span class="tag">' + E(shortFile(cu.f)) + '</span>' : '') + ' <span class="small muted">' + (k === 'ref' ? '참조' : k === 'guess' ? '추정' : '호출') + '</span></div>';
      const co = (cu.ai && S.ai && cu.ai.s) || (cu.st && cu.st.one) || '';
      if(co) h += '<div class="small muted">' + E(shortTxt(co, 72)) + '</div>';
      (lns || []).slice(0, 2).forEach(ln => { h += codeSnippetHtml(u.f, ln); });
      h += '</div>';
    });
  }
  h += '</div>';

  // Card 3: 시작점별 실행 시나리오 트리 (접이식)
  const kTree = 'flow:tree', treeFold = S.foldedCards.has(kTree);
  h += '<div class="card"><h4 class="card-tog" data-fc="' + kTree + '" style="' + (treeFold ? 'margin-bottom:0' : '') + '">' + (treeFold ? '▸ ' : '▾ ') + '🌲 시작점별 실행 시나리오<span class="sp"></span><span class="muted small">클릭 시 이동</span></h4>';
  if(!treeFold){
    let entries = U.filter(x => x.en && x.k !== 'c');
    if(!entries.length) entries = U.filter(x => x.k === 'f' && !(x.ca || []).length && (x.co || []).length);
    if(!entries.length && path.length) entries = [U[path[0].id]];
    const reachRoot = path.length ? path[0].id : -1;
    entries.sort((a, b) => (a.id === reachRoot ? -1 : b.id === reachRoot ? 1 : (b.co || []).length - (a.co || []).length));
    const renderNode = (id, depth, parentFile, seen) => {
      const nu = U[id]; if(!nu) return '';
      const xf = parentFile >= 0 && nu.f !== parentFile;
      let out = '<div class="tree-line' + (nu.id === u.id ? ' cur' : '') + '" data-gu="' + nu.id + '" style="padding-left:' + (depth * 14 + 4) + 'px">' + (nu.id === u.id ? '★ ' : (depth ? '└ ' : '▶ ')) + '[' + E(shortFile(nu.f)) + '] ' + E(nu.dn) + (xf ? ' <span class="tag">다른 파일</span>' : '') + (seen.has(id) ? ' <span class="muted">(재귀/생략)</span>' : '') + '</div>';
      if(seen.has(id) || depth >= 3) return out;
      const nextSeen = new Set(seen); nextSeen.add(id);
      sortE(nu.co).filter(e => e[1] !== 'guess').slice(0, 6).forEach(([cid]) => { out += renderNode(cid, depth + 1, nu.f, nextSeen); });
      return out;
    };
    entries.slice(0, 4).forEach((en, i) => {
      if(i > 0) h += '<div style="margin-top:6px"></div>';
      h += renderNode(en.id, 0, -1, new Set());
    });
  }
  h += '</div>';

  // Card 4: 함수·클래스 상세 명세 & 미니 그래프 (접이식)
  const kSpec = 'flow:spec', specFold = S.foldedCards.has(kSpec);
  h += '<div class="card"><h4 class="card-tog" data-fc="' + kSpec + '" style="' + (specFold ? 'margin-bottom:0' : '') + '">' + (specFold ? '▸ ' : '▾ ') + '📋 함수·클래스 상세 명세 & 미니 그래프<span class="sp"></span><span class="tag">' + UK[u.k] + '</span></h4>';
  if(!specFold){
    h += '<div class="mono small" style="margin-bottom:4px;word-break:break-all"><b>' + E(u.sig || u.dn) + '</b></div>';
    h += '<div class="small muted">' + E(FS[u.f].path) + ':' + u.l + '–' + u.e + ' <a class="chip" data-gl="' + u.l + '">코드로 이동</a></div>';
    const fl = []; if(u.en) fl.push('<span class="tag ent">진입점</span>'); if(u.rc) fl.push('<span class="tag rec">재귀</span>'); if(u.cy && !u.rc) fl.push('<span class="tag rec">순환 호출</span>'); if(u.dd) fl.push('<span class="tag dead">미사용 후보</span>');
    (u.dc || []).forEach(d => fl.push('<span class="tag">@' + E(d) + '</span>'));
    if(fl.length) h += '<div style="margin:5px 0">' + fl.join(' ') + '</div>';
    h += '<div style="height:210px;margin:8px 0;border:1px solid var(--bd);border-radius:8px;overflow:hidden"><svg id="fsvg" style="width:100%;height:100%;display:block;background:var(--code)"></svg></div>';
    if(u.st){
      h += '<div class="small" style="margin:4px 0"><b>정적 요약 ' + stBadge + ':</b> ' + md(u.st.one || '') + '</div>';
      if(u.st.bul && u.st.bul.length) h += '<ul class="small" style="margin:4px 0;padding-left:18px">' + u.st.bul.map(b => '<li>' + md(b) + '</li>').join('') + '</ul>';
    }
    if(u.m){
      const m = u.m;
      h += '<div class="grid" style="margin-top:8px"><div class="kpi"><b>' + m.lines + '</b>줄</div><div class="kpi"><b>' + m.cc + '</b>복잡도</div><div class="kpi"><b>' + m.depth + '</b>중첩</div><div class="kpi"><b>' + m.calls + '</b>호출</div></div>';
      h += '<div class="bar" style="margin-top:6px"><i class="' + dcls(m.diff) + '" style="width:' + (m.diff * 20) + '%"></i></div>';
      if(u.ef && u.ef.length) h += '<div style="margin-top:6px">' + u.ef.map(e => '<span class="tag">' + E(EFF[e] || e) + '</span>').join(' ') + '</div>';
    }
    if(u.k === 'c'){
      if(u.bs && u.bs.length) h += '<div class="small muted" style="margin-top:6px">상속: ' + u.bs.map(b => '<span class="chip" data-gu="' + b + '">' + E(U[b].dn) + '</span>').join('') + '</div>';
      if(u.at && u.at.length){ h += '<div class="small muted" style="margin-top:6px">속성 (' + u.at.length + ')</div><table><tr><th>이름</th><th>타입</th><th>정의</th></tr>'; u.at.slice(0, 20).forEach(a => { h += '<tr class="cl"><td class="mono">' + E(a[0]) + '</td><td class="mono">' + E(a[1] || '?') + '</td><td class="small"><a class="chip" data-gl="' + a[3] + '">L' + a[3] + '</a> ' + E(a[2]) + '</td></tr>'; }); h += '</table>'; }
      if(u.ch && u.ch.length) h += '<div class="small muted" style="margin-top:6px">메서드: ' + u.ch.map(c => '<span class="chip" data-gu="' + c + '">' + E(U[c].n) + '</span>').join('') + '</div>';
    }
    if(u.ol && u.ol.length){
      h += '<div class="small muted" style="margin-top:8px">제어 흐름 뼈대</div><div class="ol">';
      u.ol.forEach(o => { h += '<div class="k-' + o.k + '" data-gl="' + o.l + '" style="padding-left:' + (o.d * 14 + 4) + 'px"><span class="muted">' + o.l + '</span> ' + E(o.t) + (o.c ? ' <span class="muted">→ ' + E(o.c.join(', ')) + '</span>' : '') + '</div>'; });
      h += '</div>';
    }
    if(u.va && u.va.length){
      h += '<div class="small muted" style="margin-top:8px">변수 (' + u.va.length + '개 · 클릭하면 강조)</div><table><tr><th>이름</th><th>종류</th><th>타입</th><th>정의/사용</th></tr>';
      u.va.slice(0, 45).forEach(v => { h += '<tr class="cl" data-var="' + E(v[0]) + '"><td class="mono">' + E(v[0]) + '</td><td class="small">' + E({param:'인자',local:'지역',attr:'속성',import:'import',def:'def',comp:'내부',global:'전역'}[v[1]] || v[1]) + '</td><td class="mono small">' + E(v[2] || '?') + '</td><td class="small">' + v[3].length + ' / ' + v[4].length + '</td></tr>'; });
      h += '</table>';
    }
    if((u.xc && u.xc.length) || (u.ex && u.ex.length)){
      h += '<div class="small muted" style="margin-top:8px">외부 의존</div>';
      (u.xc || []).forEach(x => { h += '<div class="small"><code>' + E(x[0]) + '</code> ×' + x[1] + ' <span class="muted">' + E(x[2]) + '</span></div>'; });
      const libs = (u.ex || []).filter(e => e[1] === 'lib').map(e => e[0] + '→' + e[2]); if(libs.length) h += '<div class="small muted" style="margin-top:4px">모듈 별칭: ' + E(libs.join(', ')) + '</div>';
    }
    h += '<div style="display:flex;gap:6px;flex-wrap:wrap;margin-top:10px"><button data-act="pf">함수 설명 프롬프트 복사</button><button data-act="focus">이 함수만 보기</button><button data-act="graph">전체 그래프 보기</button></div>';
  }
  h += '</div>';
  return h;
}
function wireTutor(box){
  wireTraceControls(box);
  const fb = $('#fBack', box); if(fb) fb.onclick = () => histMove(-1);
  const ff = $('#fFwd', box); if(ff) ff.onclick = () => histMove(1);
  $$('[data-gu]', box).forEach(e => e.onclick = ev => { ev.stopPropagation(); gotoUnit(+e.dataset.gu); });
  $$('[data-gl]', box).forEach(e => e.onclick = ev => { ev.stopPropagation(); gotoLine(U[S.unit].f, +e.dataset.gl); });
  $$('[data-fc]', box).forEach(e => e.onclick = () => { const k = e.dataset.fc; if(S.foldedCards.has(k)) S.foldedCards.delete(k); else S.foldedCards.add(k); renderTutor(); });
  $$('[data-var]', box).forEach(e => e.onclick = () => { S.varSel = S.varSel === e.dataset.var ? null : e.dataset.var; applyVar(); renderTutor(); });
  const clv = $('[data-clr-var]', box); if(clv) clv.onclick = ev => { ev.stopPropagation(); S.varSel = null; applyVar(); renderTutor(); };
  $$('[data-act]', box).forEach(e => e.onclick = () => {
    const a = e.dataset.act;
    if(a === 'pl') copyText(promptFor('line')); else if(a === 'pf') copyText(promptFor('func'));
    else if(a === 'clrvar'){ S.varSel = null; applyVar(); renderTutor(); }
    else if(a === 'focus'){ S.focus = true; $('#bFocus').classList.add('on'); gotoLine(U[S.unit].f, U[S.unit].l, {push:false}); }
    else if(a === 'graph'){ $('#gScope').value = 'unit'; setTab('graph'); }
  });
  const fsvg = $('#fsvg', box);
  if(S.tutTab === 'flow' && fsvg){ drawGraphInto(fsvg, ego(S.unit, 1, 'both', true), {fit:true, mini:true}); }
}

/* ───────────── 그래프 (자체 레이아웃 · 외부 라이브러리 없음) ───────────── */
function layout(nodes, edges, opt){
  opt = opt || {};
  const maxPerRow = opt.maxPerRow || 10;
  const idx = new Map(nodes.map((n, i) => [n.id, i])); const N = nodes.length;
  const out = nodes.map(() => []), inn = nodes.map(() => []);
  const state = new Array(N).fill(0); const E2 = [];
  edges.forEach(e => { const a = idx.get(e.s), b = idx.get(e.t); if(a === undefined || b === undefined || a === b) return; E2.push([a, b, e]); out[a].push(b); });
  const back = new Set();
  for(let r = 0; r < N; r++){ if(state[r]) continue; const st = [[r, 0]]; state[r] = 1;
    while(st.length){ const top = st[st.length - 1]; const v = top[0]; if(top[1] < out[v].length){ const w = out[v][top[1]++]; if(state[w] === 0){ state[w] = 1; st.push([w, 0]); } else if(state[w] === 1) back.add(v + ',' + w); } else { state[v] = 2; st.pop(); } } }
  const dag = E2.map(([a, b]) => back.has(a + ',' + b) ? [b, a] : [a, b]);
  const indeg = new Array(N).fill(0), adj = nodes.map(() => []);
  dag.forEach(([a, b]) => { adj[a].push(b); indeg[b]++; });
  const layer = new Array(N).fill(0), q = []; for(let i = 0; i < N; i++) if(!indeg[i]) q.push(i);
  const deg = indeg.slice(); while(q.length){ const v = q.shift(); adj[v].forEach(w => { layer[w] = Math.max(layer[w], layer[v] + 1); if(--deg[w] === 0) q.push(w); }); }
  const L = Math.max(0, ...layer) + 1; const rows = Array.from({length: L}, () => []);
  for(let i = 0; i < N; i++) rows[layer[i]].push(i);
  const pos = new Array(N).fill(0); rows.forEach(r => r.forEach((v, i) => pos[v] = i));
  const up = nodes.map(() => []), dn = nodes.map(() => []); dag.forEach(([a, b]) => { dn[a].push(b); up[b].push(a); });
  for(let it = 0; it < 6; it++){
    const seq = it % 2 ? [...rows.keys()].reverse() : [...rows.keys()];
    seq.forEach(li => { const nb = it % 2 ? dn : up; const r = rows[li]; const bc = v => { const ns = nb[v]; return ns.length ? ns.reduce((s, w) => s + pos[w], 0) / ns.length : pos[v]; }; r.sort((x, y) => bc(x) - bc(y)); r.forEach((v, i) => pos[v] = i); });
  }
  const wrows = [];
  rows.forEach(r => {
    if(r.length <= maxPerRow){ wrows.push(r); return; }
    for(let i = 0; i < r.length; i += maxPerRow) wrows.push(r.slice(i, i + maxPerRow));
  });
  const W = 176, H = 40, GX = 22, GY = 62; const maxw = Math.max(...wrows.map(r => r.length)) * (W + GX);
  const P = new Array(N);
  wrows.forEach((r, li) => { const w = r.length * (W + GX) - GX; const x0 = (maxw - w) / 2; r.forEach((v, i) => P[v] = {x: x0 + i * (W + GX), y: li * (H + GY)}); });
  return {P, W, H, idx, width: maxw, height: wrows.length * (H + GY) - GY, E2, back};
}
function ego(id, depth, dir, guess){
  const ids = new Set([id]); let frontier = [id];
  for(let d = 0; d < depth; d++){ const nxt = [];
    frontier.forEach(v => { const u = U[v];
      if(dir !== 'up') (u.co || []).forEach(([t, k]) => { if((guess || k !== 'guess') && !ids.has(t)){ ids.add(t); nxt.push(t); } });
      if(dir !== 'down') (u.ca || []).forEach(([t, k]) => { if((guess || k !== 'guess') && !ids.has(t)){ ids.add(t); nxt.push(t); } }); });
    frontier = nxt; if(ids.size > 90) break; }
  return mkUnitGraph(ids, guess);
}
function mkUnitGraph(ids, guess){
  const nodes = [], edges = [];
  ids.forEach(i => { const u = U[i]; if(!u || u.k === 'c') return; nodes.push({id: i, label: u.k === 'm' ? FS[u.f].path.split('/').pop() + ' 실행부' : u.dn, sub: FS[u.f].path.split('/').pop(), color: palette(u.f), cur: i === S.unit}); });
  const set = new Set(nodes.map(n => n.id));
  nodes.forEach(n => (U[n.id].co || []).forEach(([t, k]) => { if(set.has(t) && (guess || k !== 'guess')) edges.push({s: n.id, t, kind: k}); }));
  return {nodes, edges};
}
function drawGraphInto(svg, g, opt){
  opt = opt || {}; svg.innerHTML = '';
  if(!g.nodes.length){ svg.innerHTML = '<text x="20" y="30" fill="currentColor" style="fill:var(--mu)">표시할 연결이 없습니다.</text>'; return; }
  const doc = svg.ownerDocument || document, win = doc.defaultView || window;
  const ly = layout(g.nodes, g.edges, opt); const NS = 'http://www.w3.org/2000/svg';
  const mk = (t, a, p) => { const e = doc.createElementNS(NS, t); for(const k in a) e.setAttribute(k, a[k]); (p || svg).appendChild(e); return e; };
  const mkrId = 'ah_' + (svg.id || (opt.mini ? 'm' : 'g'));
  const defs = mk('defs', {}); const mkr = mk('marker', {id: mkrId, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse'}, defs);
  mk('path', {d: 'M1 1L9 5L1 9z', style: 'fill:var(--mu)'}, mkr);
  const gE = mk('g', {}), gN = mk('g', {}); const edgeEls = [];
  ly.E2.forEach(([a, b, e]) => { const A = ly.P[a], B = ly.P[b]; const isBack = ly.back.has(a + ',' + b);
    const x1 = A.x + ly.W / 2, y1 = isBack ? A.y : A.y + ly.H, x2 = B.x + ly.W / 2, y2 = isBack ? B.y + ly.H : B.y; const my = (y1 + y2) / 2;
    const p = mk('path', {d: 'M' + x1 + ' ' + y1 + ' C' + x1 + ' ' + my + ',' + x2 + ' ' + my + ',' + x2 + ' ' + y2, class: 'ge ' + (e.kind === 'ref' ? 'ref' : e.kind === 'guess' ? 'guess' : ''), 'marker-end': 'url(#' + mkrId + ')'}, gE);
    edgeEls.push([p, e]); });
  g.nodes.forEach((n, i) => { const P = ly.P[i]; const grp = mk('g', {class: 'gn' + (n.cur ? ' cur' : ''), transform: 'translate(' + P.x + ',' + P.y + ')', style: 'cursor:pointer'}, gN);
    mk('rect', {width: ly.W, height: ly.H, rx: 7}, grp); mk('rect', {width: 5, height: ly.H, rx: 2, style: 'fill:' + n.color + ';stroke:none'}, grp);
    const t1 = mk('text', {x: 13, y: 17}, grp); t1.textContent = n.label.length > 24 ? n.label.slice(0, 23) + '…' : n.label;
    const t2 = mk('text', {x: 13, y: 32, class: 's'}, grp); t2.textContent = n.sub || ''; const ti = mk('title', {}, grp); ti.textContent = n.label + (n.sub ? '\n' + (opt.subLabel || '파일') + ': ' + n.sub : '');
    grp.addEventListener('mouseenter', () => edgeEls.forEach(([p, e]) => p.classList.toggle('hi', e.s === n.id || e.t === n.id)));
    grp.addEventListener('mouseleave', () => edgeEls.forEach(([p]) => p.classList.remove('hi')));
    grp.addEventListener('click', ev => { ev.stopPropagation(); if(opt.onClick) opt.onClick(n); });
    grp.addEventListener('dblclick', ev => { ev.stopPropagation(); if(opt.onDbl) opt.onDbl(n); }); });
  const pad = 30; const view = {x: -pad, y: -pad, w: ly.width + pad * 2, h: ly.height + pad * 2};
  const rect = svg.getBoundingClientRect(); const ar = (rect.width || 600) / (rect.height || 400);
  if(view.w / view.h < ar){ const nw = view.h * ar; view.x -= (nw - view.w) / 2; view.w = nw; } else { const nh = view.w / ar; view.y -= (nh - view.h) / 2; view.h = nh; }
  svg._view = view; svg._fit = {...view}; const set = () => svg.setAttribute('viewBox', [view.x, view.y, view.w, view.h].join(' ')); set();
  if(opt.noPan) return;
  svg.onwheel = ev => { ev.preventDefault(); const r = svg.getBoundingClientRect(); const mx = view.x + (ev.clientX - r.left) / r.width * view.w, my = view.y + (ev.clientY - r.top) / r.height * view.h; const f = ev.deltaY < 0 ? 0.87 : 1.15; view.w *= f; view.h *= f; view.x = mx - (ev.clientX - r.left) / r.width * view.w; view.y = my - (ev.clientY - r.top) / r.height * view.h; set(); };
  let drag = null; svg.onmousedown = ev => { drag = {x: ev.clientX, y: ev.clientY, vx: view.x, vy: view.y}; svg.classList.add('pan'); };
  win.addEventListener('mousemove', svg._mm = ev => { if(!drag) return; const r = svg.getBoundingClientRect(); view.x = drag.vx - (ev.clientX - drag.x) / r.width * view.w; view.y = drag.vy - (ev.clientY - drag.y) / r.height * view.h; set(); });
  win.addEventListener('mouseup', svg._mu = () => { drag = null; svg.classList.remove('pan'); });
}
let gPopWin = null;
function graphSnap(uid){
  return {unit: uid !== undefined ? uid : S.unit, file: S.file, scope: $('#gScope').value, depth: $('#gDepth').value, dir: $('#gDir').value, guess: $('#gGuess').checked};
}
function sameGraphSnap(a, b){
  return a && b && a.unit === b.unit && a.file === b.file && a.scope === b.scope && a.depth === b.depth && a.dir === b.dir && a.guess === b.guess;
}
function pushGraphSnap(uid){
  const sn = graphSnap(uid);
  if(!S.gHist.length){ S.gHist = [sn]; S.gHi = 0; updateGraphNav(); return; }
  if(sameGraphSnap(S.gHist[S.gHi], sn)) return;
  S.gHist = S.gHist.slice(0, S.gHi + 1);
  S.gHist.push(sn);
  S.gHi = S.gHist.length - 1;
  updateGraphNav();
}
function updateGraphNav(){
  const noB = S.gHi <= 0, noF = S.gHi < 0 || S.gHi >= S.gHist.length - 1;
  if($('#gBack')) $('#gBack').disabled = noB;
  if($('#gFwd')) $('#gFwd').disabled = noF;
  if(gPopWin && !gPopWin.closed){
    const d = gPopWin.document;
    const b = d.getElementById('gBackW'), f = d.getElementById('gFwdW');
    if(b) b.disabled = noB;
    if(f) f.disabled = noF;
  }
}
function graphHistMove(delta){
  const ni = S.gHi + delta;
  if(ni < 0 || ni >= S.gHist.length) return;
  S.gHi = ni;
  const st = S.gHist[ni];
  S.unit = st.unit; S.file = st.file;
  $('#gScope').value = st.scope;
  $('#gDepth').value = st.depth;
  $('#gDir').value = st.dir;
  $('#gGuess').checked = st.guess;
  renderTutor();
  renderGraph({noHist: true});
}
function buildGraphData(){
  const scope = $('#gScope').value, depth = +$('#gDepth').value, dir = $('#gDir').value, guess = $('#gGuess').checked;
  let ids = new Set(), note = '';
  if(scope === 'unit') return {g: ego(S.unit, depth, dir, guess), note: ''};
  if(scope === 'file'){ FS[S.file].us.forEach(i => ids.add(i)); }
  else {
    U.forEach(u => { if(u.k !== 'c' && ((u.co || []).length || (u.ca || []).length)) ids.add(u.id); });
    if(ids.size > 140){
      const arr = [...ids].sort((a, b) => ((U[b].co || []).length + (U[b].ca || []).length) - ((U[a].co || []).length + (U[a].ca || []).length)).slice(0, 140);
      ids = new Set(arr);
      note = '연결이 많은 상위 140개만 표시 (전체 ' + U.filter(u => u.k !== 'c').length + '개)';
    }
  }
  const g = mkUnitGraph(ids, guess);
  g.nodes = g.nodes.filter(n => g.edges.some(e => e.s === n.id || e.t === n.id) || scope === 'file' || n.cur);
  return {g, note};
}
function graphSelectNode(id){
  if(!S.gHist.length) pushGraphSnap();
  S.unit = id;
  if(U[id]) S.file = U[id].f;
  pushGraphSnap(id);
  S.tutTab = 'flow';
  renderTutor();
  renderGraph({noHist: true});
}
function renderGraph(opt){
  opt = opt || {};
  if(!opt.noHist) pushGraphSnap();
  const {g, note} = buildGraphData();
  const infoTxt = '노드 ' + g.nodes.length + ' · 연결 ' + g.edges.length + (note ? ' · ' + note : '');
  $('#gInfo').textContent = infoTxt;
  drawGraphInto($('#gsvg'), g, {onClick: n => graphSelectNode(n.id), onDbl: n => gotoUnit(n.id)});
  updateGraphNav();
  if(gPopWin && !gPopWin.closed) syncGraphWindow(g, infoTxt);
}
function syncGraphWindow(g, infoTxt){
  if(!gPopWin || gPopWin.closed) return;
  const d = gPopWin.document;
  const sw = d.getElementById('gScopeW'), dw = d.getElementById('gDepthW'), rw = d.getElementById('gDirW'), gw = d.getElementById('gGuessW'), iw = d.getElementById('gInfoW'), svgW = d.getElementById('gsvgW');
  if(!svgW) return;
  if(sw) sw.value = $('#gScope').value;
  if(dw) dw.value = $('#gDepth').value;
  if(rw) rw.value = $('#gDir').value;
  if(gw) gw.checked = $('#gGuess').checked;
  if(iw) iw.textContent = infoTxt;
  drawGraphInto(svgW, g, {
    onClick: n => graphSelectNode(n.id),
    onDbl: n => { gotoUnit(n.id); try{ window.focus(); }catch(e){} }
  });
  updateGraphNav();
}
function openGraphWindow(){
  const sz = gLsGet('gPopSz', {w:1280, h:860});
  const pw = window.open('', 'ct_unit_graph', 'width=' + (sz.w || 1280) + ',height=' + (sz.h || 860) + ',resizable=yes');
  if(!pw){ toast('팝업이 차단되어 새 창을 열 수 없습니다 (브라우저 팝업 허용 필요)'); return; }
  gPopWin = pw;
  let _rt = null;
  pw.addEventListener('resize', () => { clearTimeout(_rt); _rt = setTimeout(() => { try{ gLsSet('gPopSz', {w: Math.max(480, pw.outerWidth || pw.innerWidth), h: Math.max(360, pw.outerHeight || pw.innerHeight)}); }catch(e){} }, 250); });
  const cls = document.documentElement.className;
  const css = ($('style') && $('style').textContent) || '';
  const gtoolHtml = $('#vGraph .gtool').innerHTML
    .replace('id="gBack"', 'id="gBackW"')
    .replace('id="gFwd"', 'id="gFwdW"')
    .replace('id="gScope"', 'id="gScopeW"')
    .replace('id="gDepth"', 'id="gDepthW"')
    .replace('id="gDir"', 'id="gDirW"')
    .replace('id="gFit"', 'id="gFitW"')
    .replace('id="gPop"', 'id="gPopW" style="display:none"')
    .replace('id="gGuess"', 'id="gGuessW"')
    .replace('id="gInfo"', 'id="gInfoW"');
  const d = pw.document;
  d.open();
  d.write('<!doctype html><html class="' + E(cls) + '"><head><meta charset="utf-8"><title>' + E(D.title) + ' — 호출 그래프</title><style>' + css + '\nhtml,body{height:100%;margin:0;overflow:hidden}#gWinWrap{height:100vh;display:flex;flex-direction:column;background:var(--bg2)}#gsvgW{flex:1;width:100%;height:100%;display:block;background:var(--code);cursor:grab}#gsvgW.pan{cursor:grabbing}</style></head><body><div id="gWinWrap"><div class="gtool">' + gtoolHtml + '</div><div style="flex:1;min-height:0"><svg id="gsvgW"></svg></div></div></body></html>');
  d.close();
  const bindSel = (wid, mid) => {
    const el = d.getElementById(wid);
    if(el) el.onchange = () => { $('#' + mid).value = el.value; pushGraphSnap(); renderGraph({noHist: true}); };
  };
  bindSel('gScopeW', 'gScope');
  bindSel('gDepthW', 'gDepth');
  bindSel('gDirW', 'gDir');
  const gw = d.getElementById('gGuessW');
  if(gw) gw.onchange = () => { $('#gGuess').checked = gw.checked; pushGraphSnap(); renderGraph({noHist: true}); };
  const bw = d.getElementById('gBackW'), fw = d.getElementById('gFwdW'), fitW = d.getElementById('gFitW'), svgW = d.getElementById('gsvgW');
  if(bw) bw.onclick = () => graphHistMove(-1);
  if(fw) fw.onclick = () => graphHistMove(1);
  if(fitW) fitW.onclick = () => { if(svgW && svgW._fit){ Object.assign(svgW._view, svgW._fit); svgW.setAttribute('viewBox', [svgW._fit.x, svgW._fit.y, svgW._fit.w, svgW._fit.h].join(' ')); } };
  if(svgW) svgW.addEventListener('mouseup', ev => { if(ev.button === 3){ ev.preventDefault(); graphHistMove(-1); } else if(ev.button === 4){ ev.preventDefault(); graphHistMove(1); } });
  d.addEventListener('keydown', ev => {
    const tag = (d.activeElement && d.activeElement.tagName) || '';
    if(tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') return;
    if(ev.key === 'Backspace'){ ev.preventDefault(); graphHistMove(-1); }
  });
  const {g, note} = buildGraphData();
  const infoTxt = '노드 ' + g.nodes.length + ' · 연결 ' + g.edges.length + (note ? ' · ' + note : '');
  syncGraphWindow(g, infoTxt);
  pw.focus();
}

/* ───────────── 개요 ───────────── */
function renderOverview(){
  const s = D.stats, ai = D.ai, ov = ai && ai.ov;
  const langCnt = {}; FS.forEach(f => { const lg = f.lang || 'py'; langCnt[lg] = (langCnt[lg] || 0) + 1; });
  const langKeys = Object.keys(langCnt);
  const langHtml = (langKeys.length > 1 || (langKeys[0] && langKeys[0] !== 'py'))
    ? langKeys.map(lg => '<span class="lang-tag lt-' + E(lg) + '" style="font-size:.76em;padding:2px 8px">' + E(LANG_NM[lg] || lg.toUpperCase()) + ' ' + langCnt[lg] + '파일</span>').join('')
    : '';
  let h = '<h2 style="display:flex;align-items:center;gap:6px;flex-wrap:wrap"><span>프로젝트 한눈에</span>' + (langHtml ? '<span class="sp"></span>' + langHtml : '') + '</h2>';
  h += '<div class="grid"><div class="kpi"><b>' + s.files + '</b><span>파일</span></div><div class="kpi"><b>' + s.lines.toLocaleString() + '</b><span>줄</span></div><div class="kpi"><b>' + s.classes + '</b><span>클래스</span></div><div class="kpi"><b>' + s.funcs + '</b><span>함수·메서드</span></div></div>';
  h += '<div class="card" style="margin-top:10px"><h4>요약 ' + stBadge + '</h4>' + fmtSummary(D.so.s) + (D.so.f ? '<div class="ov-flow"><div class="hint" style="margin:0">추정 읽기 흐름: ' + md(D.so.f) + '</div></div>' : '') + '</div>';
  if(ov && S.ai){ h += '<div class="card"><h4>AI 개요 ' + aiBadge(ov) + '<span class="sp"></span><span class="muted small">' + E(ov.m || '') + '</span></h4>' + fmtSummary(ov.s) + (ov.f ? '<div class="ov-flow"><div class="hint" style="margin:0">' + md(ov.f) + '</div></div>' : '') + '</div>'; }
  const st = ai && ai.stats;
  if(st && st.enabled){ h += '<div class="card small muted">AI 해설: 대상 ' + st.targets + '개 · 검증 통과 ' + st.ok + ' · 일부 미검증 ' + st.partial + ' · 거부(정적 해설로 대체) ' + st.rejected + ' · 실패 ' + st.failed + ' · 캐시 ' + st.cached + (st.stopped ? '<br>⚠ ' + E(st.stopped) : '') + '</div>'; }
  else if(st && st.stopped){ h += '<div class="card small muted">AI 해설 사용 안 함: ' + E(st.stopped) + ' — 모든 해설은 정적 분석으로 제공됩니다.</div>'; }
  if(D.errors && D.errors.length) h += '<div class="card small muted">일부 문장 분석 실패 ' + D.errors.length + '건: ' + E(D.errors[0]) + '</div>';
  h += '<h2 style="display:flex;align-items:center;gap:6px;flex-wrap:wrap"><span>파일 의존 관계</span><span class="muted small" id="ovGraphStat" style="font-weight:400"></span><span class="legend-item" style="font-size:.76em;font-weight:500;color:var(--tx);background:var(--code);border:1px solid var(--bd);border-radius:7px;padding:2px 7px" title="각 박스 왼쪽 세로 막대 색상은 파일을 구분합니다.&#10;(같은 색 = 같은 파일)"><svg width="15" height="11" aria-hidden="true"><rect x="1" y="1" width="3" height="9" rx="1" fill="#4cc2ff"/><rect x="6" y="1" width="3" height="9" rx="1" fill="#ffd866"/><rect x="11" y="1" width="3" height="9" rx="1" fill="#7ee787"/></svg> 파일별 색</span><span class="sp"></span><label class="gchk" style="font-size:.76em;padding:2px 8px;font-weight:500" title="다른 파일과 연결이 없는 고립 파일도 함께 표시합니다"><input type="checkbox" id="ovIsoChk"> 고립 파일 포함</label><button id="bOvGraphPop" style="font-size:.78em;padding:3px 9px" title="파일 의존 관계 그래프를 별도 창으로 띄웁니다 (다른 모니터 이동 가능)">↗ 새 창으로</button></h2><div class="card" style="height:' + Math.min(420, 140 + FS.length * 18) + 'px;padding:0"><svg id="osvg" style="background:var(--code);width:100%;height:100%;display:block;border-radius:10px"></svg></div>';
  const hot = U.filter(u => u.k === 'f').sort((a, b) => b.m.diff - a.m.diff || b.m.cc - a.m.cc).slice(0, 10);
  h += '<h2>읽기 어려운 함수 TOP 10</h2><div class="card"><table><tr><th>함수</th><th>난이도</th><th>복잡도</th><th>줄</th><th>중첩</th></tr>' + hot.map(u => '<tr class="cl" data-gu="' + u.id + '"><td class="mono">' + E(u.dn) + '</td><td><span class="dot ' + dcls(u.m.diff) + '"></span> ' + u.m.diff + '</td><td>' + u.m.cc + '</td><td>' + u.m.lines + '</td><td>' + u.m.depth + '</td></tr>').join('') + '</table></div>';
  const order = D.order.down.slice(0, 10);
  h += '<h2>추천 읽기 순서 (위에서 아래로)</h2><div class="card">' + order.map((id, i) => '<div class="row" data-gu="' + id + '"><span class="mt">' + (i + 1) + '</span><span class="nm mono">' + E(unitLabel(U[id])) + '</span><span class="mt">' + md(D.order.why[id] || '') + '</span></div>').join('') + '<div class="small muted" style="margin-top:6px">전체 순서는 왼쪽 [학습 순서] 탭에서 볼 수 있고, "아래에서 위로(기초부터)" 순서로도 바꿀 수 있습니다.</div></div>';
  if(s.libs && s.libs.length) h += '<h2>많이 쓰인 외부 라이브러리</h2><div class="card">' + s.libs.map(l => '<span class="tag">' + E(l[0]) + ' ×' + l[1] + '</span> ').join('') + '</div>';
  const box = $('#vOv'); box.innerHTML = h;
  $$('[data-gu]', box).forEach(e => e.onclick = () => gotoUnit(+e.dataset.gu));
  const nodes = FS.map(f => ({id: f.id, label: f.path.split('/').pop(), sub: f.path.indexOf('/') >= 0 ? f.path.split('/').slice(0, -1).join('/') : '루트 폴더', color: palette(f.id)}));
  const edges = []; FS.forEach(f => f.deps.forEach(d => edges.push({s: f.id, t: d, kind: 'call'})));
  const connected = new Set(); edges.forEach(e => { connected.add(e.s); connected.add(e.t); });
  let curOvGraph = {nodes, edges};
  const drawOvGraph = includeIso => {
    const visNodes = (includeIso || !connected.size) ? nodes : nodes.filter(n => connected.has(n.id));
    curOvGraph = {nodes: visNodes, edges};
    const statEl = $('#ovGraphStat');
    if(statEl) statEl.textContent = connected.size ? ('(연결 ' + visNodes.length + '/' + nodes.length + ')') : ('(연결 없음 · ' + nodes.length + '파일)');
    drawGraphInto($('#osvg'), curOvGraph, {onClick: n => gotoLine(n.id, 1), noPan: false, maxPerRow: 8, subLabel: '폴더'});
  };
  drawOvGraph(false);
  const isoChk = $('#ovIsoChk');
  if(isoChk) isoChk.onchange = () => drawOvGraph(isoChk.checked);
  const popBtn = $('#bOvGraphPop');
  if(popBtn) popBtn.onclick = () => {
    const sz = gLsGet('ovPopSz', {w:1280, h:860});
    const pw = window.open('', 'ct_ov_dep_graph', 'width=' + (sz.w || 1280) + ',height=' + (sz.h || 860) + ',resizable=yes');
    if(!pw){
      toast('팝업이 차단되어 모달로 엽니다');
      $('#ovGraphModal').classList.add('show');
      drawGraphInto($('#osvgPop'), curOvGraph, {onClick: n => { $('#ovGraphModal').classList.remove('show'); gotoLine(n.id, 1); }, noPan: false, maxPerRow: 10, subLabel: '폴더'});
      return;
    }
    let _rt = null;
    pw.addEventListener('resize', () => { clearTimeout(_rt); _rt = setTimeout(() => { try{ gLsSet('ovPopSz', {w: Math.max(480, pw.outerWidth || pw.innerWidth), h: Math.max(360, pw.outerHeight || pw.innerHeight)}); }catch(e){} }, 250); });
    const cls = document.documentElement.className;
    const css = ($('style') && $('style').textContent) || '';
    const d = pw.document;
    d.open();
    d.write('<!doctype html><html class="' + E(cls) + '"><head><meta charset="utf-8"><title>' + E(D.title) + ' — 파일 의존 관계</title><style>' + css + '\nhtml,body{height:100%;margin:0;overflow:hidden}#popWrap{height:100vh;display:flex;flex-direction:column;background:var(--bg2)}#popBar{height:40px;display:flex;align-items:center;gap:8px;padding:0 12px;background:var(--sub);border-bottom:1px solid var(--bd);flex-shrink:0;font-size:13px}#osvgWin{flex:1;width:100%;height:100%;display:block;background:var(--code);cursor:grab}#osvgWin.pan{cursor:grabbing}</style></head><body><div id="popWrap"><div id="popBar"><strong style="color:var(--ac)">파일 의존 관계</strong><span class="muted small">(위 → 아래: import 방향 · 휠: 확대/축소 · 드래그: 이동 · 클릭: 원래 창에서 열기)</span><span style="flex:1"></span><button id="bPopFit">화면 맞춤</button></div><svg id="osvgWin"></svg></div></body></html>');
    d.close();
    const sEl = d.getElementById('osvgWin');
    drawGraphInto(sEl, curOvGraph, {onClick: n => { gotoLine(n.id, 1); try{ window.focus(); }catch(e){} }, noPan: false, maxPerRow: 10, subLabel: '폴더'});
    const fitBtn = d.getElementById('bPopFit');
    if(fitBtn) fitBtn.onclick = () => { if(sEl._fit){ Object.assign(sEl._view, sEl._fit); sEl.setAttribute('viewBox', [sEl._fit.x, sEl._fit.y, sEl._fit.w, sEl._fit.h].join(' ')); } };
    pw.focus();
  };
}

/* ───────────── 사이드바 ───────────── */
function matchQ(s){ return !S.filter || s.toLowerCase().includes(S.filter.toLowerCase()); }
function unitRow(u, depth, isParent, childClosed){
  const act = u.id === S.unit ? ' act' : '';
  const hasPin = (S.pins[String(u.id)] || []).length > 0;
  const hasChat = (S.threads[String(u.id)] || []).length > 0;
  const isBmk = (S.bookmarks || []).includes(u.id);
  const isDn = (S.done || []).includes(u.id);
  const tog = isParent ? '<span class="utog" data-tu="' + u.id + '" title="하위 접기/펼치기">' + (childClosed ? '▸' : '▾') + '</span>' : '<span style="display:inline-block;width:14px"></span>';
  const marks = (isBmk ? '<span title="북마크">⭐</span>' : '') + (hasPin ? '<span title="고정 노트">📌</span>' : '') + (hasChat ? '<span title="질문 기록">💬</span>' : '') + (isDn ? '<span style="color:var(--ok)" title="학습 완료">✓</span>' : '');
  return '<div class="row' + act + '" data-gu="' + u.id + '" style="padding-left:' + (6 + depth * 12) + 'px" title="' + E(u.st.one || '') + '">' + tog + '<span class="dot ' + (u.m ? dcls(u.m.diff) : '') + '"></span><span class="nm mono">' + (u.k === 'c' ? '◆ ' : '') + E(u.n) + '</span>' + marks + (u.en ? '<span class="tag ent">진입</span>' : '') + (u.dd ? '<span class="tag dead">미사용?</span>' : '') + (u.ai ? '<span class="aid" title="AI 해설 있음">●</span>' : '') + '<span class="mt">' + (u.m ? u.m.lines : '') + '</span></div>';
}
function renderSide(light){
  const box = $('#sidec');
  if(light && box.children.length && (S.sideTab === 'files' || S.sideTab === 'order' || S.sideTab === 'review')){
    $$('.row.act[data-gu]', box).forEach(e => e.classList.remove('act'));
    const cur = $('.row[data-gu="' + S.unit + '"]', box);
    if(cur) cur.classList.add('act');
    return;
  }
  $$('.sidetabs button').forEach(b => b.classList.toggle('on', b.dataset.st === S.sideTab));
  const keep = box.scrollTop; let h = '';
  if(S.sideTab === 'files'){
    const multiLang = FS.some(x => x.lang && x.lang !== 'py');
    h += '<div class="treebar"><button data-tree-act="collapse">하위 모두 접기</button><button data-tree-act="expand">모두 펴기</button></div>';
    const dirs = {}; FS.forEach(f => { const d = f.path.includes('/') ? f.path.split('/').slice(0, -1).join('/') : ''; (dirs[d] = dirs[d] || []).push(f); });
    Object.keys(dirs).sort().forEach(d => {
      const fl = dirs[d].filter(f => matchQ(f.path) || f.us.some(i => matchQ(U[i].dn))); if(!fl.length) return;
      const dClosed = d && S.closedDirs.has(d) && !S.filter;
      if(d) h += '<div class="dir cl" data-td="' + E(d) + '">' + (dClosed ? '▸ ' : '▾ ') + '📁 ' + E(d) + '</div>';
      if(dClosed) return;
      fl.forEach(f => {
        const open = S.open.has(f.id) || f.id === S.file || !!S.filter;
        const lg = f.lang || 'py';
        const lbadge = multiLang ? '<span class="lang-tag lt-' + E(lg) + '">' + E(LANG_TAG[lg] || lg.toUpperCase()) + '</span>' : '';
        h += '<div class="row' + (f.id === S.file ? ' act' : '') + '" data-gf="' + f.id + '"><span>' + (open ? '▾' : '▸') + '</span>' + lbadge + '<span class="nm mono">' + E(f.path.split('/').pop()) + '</span><span class="mt">' + f.n + '줄</span></div>';
        if(open){
          const ul = f.us.map(i => U[i]).filter(u => u.k !== 'm' && (matchQ(u.dn) || matchQ(f.path)));
          const hasKids = new Set();
          ul.forEach(u => { if(u.p >= 0 && U[u.p] && U[u.p].k !== 'm') hasKids.add(u.p); if(u.k === 'c' && u.ch && u.ch.length) hasKids.add(u.id); });
          ul.forEach(u => {
            let depth = 0, p = U[u.p], hide = false;
            while(p && p.k !== 'm'){ if(!S.filter && S.closedUnits.has(p.id)) hide = true; depth++; p = U[p.p]; }
            if(!hide) h += unitRow(u, depth, hasKids.has(u.id), S.closedUnits.has(u.id));
          });
          const mu = U[f.mu]; if(mu && mu.co && mu.co.length) h += '<div class="row' + (mu.id === S.unit ? ' act' : '') + '" data-gu="' + mu.id + '" style="padding-left:22px"><span class="nm">▶ 모듈 실행부</span></div>';
        }
      });
    });
  } else if(S.sideTab === 'order'){
    const arr = D.order[S.order]; const done = new Set((S.done && S.done.length) ? S.done : lsGet('done', []));
    h += '<div class="pad"><button class="' + (S.order === 'down' ? 'on' : '') + '" data-ord="down">위에서 아래로</button> <button class="' + (S.order === 'up' ? 'on' : '') + '" data-ord="up">기초부터(아래→위)</button><div class="small muted" style="margin-top:6px">' + (S.order === 'down' ? '진입점에서 시작해 호출을 따라 내려갑니다. 전체 그림을 먼저 잡기 좋습니다.' : '남을 호출하지 않는 말단 함수부터 읽습니다. 부품을 먼저 이해하고 올라가기 좋습니다.') + '</div></div>';
    arr.forEach((id, i) => { const u = U[id]; if(!matchQ(u.dn)) return; h += '<div class="row' + (id === S.unit ? ' act' : '') + '" data-gu="' + id + '"><input type="checkbox" data-done="' + id + '"' + (done.has(id) ? ' checked' : '') + '><span class="mt">' + (i + 1) + '</span><span class="nm mono" style="' + (done.has(id) ? 'text-decoration:line-through;opacity:.6' : '') + '">' + E(unitLabel(u)) + '</span><span class="dot ' + dcls(u.m.diff) + '"></span></div>'; });
  } else if(S.sideTab === 'review'){
    const funcs = U.filter(u => u.k === 'f');
    const doneSet = new Set(S.done || []);
    const pct = funcs.length ? Math.round(doneSet.size * 100 / funcs.length) : 0;
    h += '<div class="pad">';
    if(S.last && U[S.last.unit_id]){
      const lu = U[S.last.unit_id];
      h += '<div class="card" style="margin-bottom:8px"><h4>📖 마지막 학습 이어하기</h4><div class="mono small">' + E(unitLabel(lu)) + '</div><div class="small muted">L' + (S.last.line || lu.l) + (S.last.ts ? ' · ' + E(S.last.ts) : '') + '</div><button data-resume="1" style="margin-top:6px;width:100%">이어서 열기 ▶</button></div>';
    }
    h += '<div class="card" style="margin-bottom:8px"><h4>📊 학습 진도 (' + doneSet.size + ' / ' + funcs.length + ' · ' + pct + '%)</h4><div class="bar"><i class="d1" style="width:' + pct + '%"></i></div></div>';
    h += '</div>';
    const bmkU = (S.bookmarks || []).map(id => U[id]).filter(Boolean);
    const pinU = Object.keys(S.pins || {}).filter(k => (S.pins[k] || []).length > 0).map(k => U[+k]).filter(Boolean);
    const chatU = Object.keys(S.threads || {}).filter(k => (S.threads[k] || []).length > 0).map(k => U[+k]).filter(Boolean);
    const secR = (t, arr, sub) => { h += '<div class="dir">' + t + ' (' + arr.length + ')</div>'; if(!arr.length) h += '<div class="small muted" style="padding:2px 12px">없음</div>'; arr.forEach(u => h += '<div class="row' + (u.id === S.unit ? ' act' : '') + '" data-gu="' + u.id + '"><span class="nm mono">' + E(unitLabel(u)) + '</span><span class="mt">' + sub(u) + '</span></div>'); };
    secR('⭐ 복습 북마크', bmkU, u => (u.m ? u.m.lines + '줄' : ''));
    secR('📌 고정 노트가 있는 함수', pinU, u => (S.pins[String(u.id)] || []).length + '개');
    secR('💬 1:1 질문 기록', chatU, u => Math.floor((S.threads[String(u.id)] || []).length / 2) + '문답');
  } else {
    const fu = U.filter(u => u.k === 'f' && matchQ(u.dn)); const sec = (t, arr, sub) => { h += '<div class="dir">' + t + '</div>'; if(!arr.length) h += '<div class="small muted" style="padding:2px 12px">없음</div>'; arr.forEach(u => h += '<div class="row" data-gu="' + u.id + '"><span class="dot ' + dcls(u.m.diff) + '"></span><span class="nm mono">' + E(u.dn) + '</span><span class="mt">' + sub(u) + '</span></div>'); };
    sec('어려운 함수 (난이도·복잡도)', fu.slice().sort((a, b) => b.m.diff - a.m.diff || b.m.cc - a.m.cc).slice(0, 12), u => 'cc ' + u.m.cc);
    sec('가장 많이 호출되는 함수', fu.slice().sort((a, b) => b.m.callers - a.m.callers).filter(u => u.m.callers > 0).slice(0, 10), u => u.m.callers + '곳');
    sec('진입점', fu.filter(u => u.en).slice(0, 10), u => u.m.callees + '호출');
    sec('미사용 후보 (호출하는 곳 없음)', fu.filter(u => u.dd).slice(0, 12), u => u.m.lines + '줄');
    sec('재귀·순환 호출', fu.filter(u => u.rc || u.cy).slice(0, 10), u => u.rc ? '재귀' : '순환');
  }
  box.innerHTML = h; box.scrollTop = keep;
  $$('[data-tu]', box).forEach(e => e.onclick = ev => { ev.stopPropagation(); const id = +e.dataset.tu; if(S.closedUnits.has(id)) S.closedUnits.delete(id); else S.closedUnits.add(id); renderSide(); });
  $$('[data-td]', box).forEach(e => e.onclick = () => { const d = e.dataset.td; if(S.closedDirs.has(d)) S.closedDirs.delete(d); else S.closedDirs.add(d); renderSide(); });
  $$('[data-tree-act]', box).forEach(e => e.onclick = () => {
    if(e.dataset.treeAct === 'collapse'){
      U.forEach(u => { if(u.k === 'c' || (u.p >= 0 && U[u.p] && U[u.p].k !== 'm')) { if(u.k === 'c') S.closedUnits.add(u.id); else if(U[u.p].k !== 'm') S.closedUnits.add(u.p); } });
      S.open.clear(); S.open.add(S.file);
    } else {
      S.closedUnits.clear(); S.closedDirs.clear(); FS.forEach(f => S.open.add(f.id));
    }
    renderSide();
  });
  const resBtn = $('[data-resume]', box);
  if(resBtn && S.last) resBtn.onclick = () => {
    if(S.last.step_id) selectStep(S.last.unit_id, S.last.step_id);
    else gotoLine(S.last.file_id || U[S.last.unit_id].f, S.last.line || U[S.last.unit_id].l);
  };
  $$('[data-gu]', box).forEach(e => e.onclick = () => gotoUnit(+e.dataset.gu));
  $$('[data-gf]', box).forEach(e => e.onclick = () => { const id = +e.dataset.gf; if(S.open.has(id) && id !== S.file) S.open.delete(id); else S.open.add(id); gotoLine(id, 1); });
  $$('[data-ord]', box).forEach(e => e.onclick = ev => { ev.stopPropagation(); S.order = e.dataset.ord; renderSide(); });
  $$('[data-done]', box).forEach(e => e.onclick = ev => { ev.stopPropagation(); const s = new Set(S.done || []); const id = +e.dataset.done; if(e.checked) s.add(id); else s.delete(id); S.done = [...s]; saveStudyState({done: S.done}); renderSide(); });
}

/* ───────────── 탭/검색/이벤트 ───────────── */
function setTab(t){
  S.tab = t; $$('.tabs button').forEach(b => b.classList.toggle('on', b.dataset.tab === t));
  $('#vOv').style.display = t === 'ov' ? 'block' : 'none'; $('#vGraph').style.display = t === 'graph' ? 'flex' : 'none'; $('#codewrap').style.display = t === 'code' ? 'flex' : 'none';
  if(t === 'ov') renderOverview(); if(t === 'graph') renderGraph();
  if(t === 'code' && renderedFile !== S.file){ renderCode(); }
  if(t === 'code'){ selectLine(S.line, {noscroll: false}); }
}
function openPalette(){ $('#pal').classList.add('show'); const i = $('#palIn'); i.value = ''; i.focus(); palList(''); }
function palList(q){
  q = q.toLowerCase(); const res = [];
  U.forEach(u => { if(u.k === 'm') return; const n = u.dn.toLowerCase(); const sc = !q ? 1 : n === q ? 100 : n.startsWith(q) || u.n.toLowerCase().startsWith(q) ? 50 : n.includes(q) ? 20 : 0; if(sc) res.push({sc, t: (u.k === 'c' ? '◆ ' : 'ƒ ') + u.dn, sub: FS[u.f].path + ':' + u.l, go: () => gotoUnit(u.id)}); });
  FS.forEach(f => { const p = f.path.toLowerCase(); if(q && p.includes(q)) res.push({sc: 15, t: '📄 ' + f.path, sub: f.n + '줄', go: () => gotoLine(f.id, 1)}); });
  res.sort((a, b) => b.sc - a.sc); const top = res.slice(0, 40); $('#palRes').innerHTML = top.map((r, i) => '<div class="row" data-i="' + i + '"><span class="nm mono">' + E(r.t) + '</span><span class="mt">' + E(r.sub) + '</span></div>').join('');
  $$('#palRes .row').forEach(e => e.onclick = () => { $('#pal').classList.remove('show'); top[+e.dataset.i].go(); }); palList.top = top;
}
function initSplit(id, varName, side){
  const key = varName === '--sw' ? 'sw' : 'tw';
  const saved = gLsGet(key, 0);
  if(saved && saved >= 180 && saved <= Math.max(360, window.innerWidth * 0.7)) document.documentElement.style.setProperty(varName, saved + 'px');
  const sp = $(id); let drag = false, lastW = 0;
  sp.addEventListener('mousedown', e => {
    if(e.target.closest('.spbtn')) return;
    drag = true; sp.classList.add('drag'); document.body.classList.add('resizing');
    if(side === 'l' && S.hideL) togglePanel('l', false);
    if(side === 'r' && S.hideR) togglePanel('r', false);
    e.preventDefault();
  });
  window.addEventListener('mouseup', () => {
    if(drag && lastW >= 180) gLsSet(key, Math.round(lastW));
    drag = false; sp.classList.remove('drag'); document.body.classList.remove('resizing');
  });
  window.addEventListener('mousemove', e => {
    if(!drag) return;
    lastW = Math.max(180, Math.min(window.innerWidth * 0.58, side === 'l' ? e.clientX : window.innerWidth - e.clientX));
    document.documentElement.style.setProperty(varName, lastW + 'px');
  });
}
function updateLlmBadge(){
  const dot = $('#llmDot'); if(!dot) return;
  const pw = S.prewarm || {};
  if(S.llmCfg && S.llmCfg.use_llm){
    const ready = !!(S.llmCfg.base_url && S.llmCfg.model);
    if(!ready){
      dot.textContent = !S.llmCfg.base_url ? 'URL 미설정' : '모델 미설정';
      dot.className = 'tag dead';
    } else if(pw.active && pw.total){
      dot.textContent = 'AI 예열 ' + pw.done + '/' + pw.total;
      dot.className = 'tag ent';
    } else {
      dot.textContent = 'AI: ' + S.llmCfg.model.slice(0, 14);
      dot.className = 'tag ent';
    }
  } else {
    dot.textContent = S.srvOk ? '정적 튜터' : '오프라인';
    dot.className = 'tag';
  }
  const pb = $('#prewarmBox');
  if(pb){
    if(pw.active) pb.textContent = '⚡ 백그라운드 기본 해설 캐시 생성 중: ' + pw.done + ' / ' + pw.total + ' (성공 ' + pw.cached + ')';
    else if(pw.total) pb.textContent = '✅ 기본 해설 캐시 준비 완료: ' + pw.cached + ' / ' + pw.total + '개';
    else pb.textContent = '';
  }
  updateAiBtn();
}
function updateAiBtn(){
  const btn = $('#bAi'); if(!btn) return;
  const hasSavedAi = !!((D.ai && D.ai.ov) || U.some(u => u && u.ai));
  const hasLlm = !!(S.llmCfg && S.llmCfg.use_llm && S.llmCfg.base_url && S.llmCfg.model);
  const avail = hasSavedAi || hasLlm;
  btn.disabled = !avail;
  btn.classList.toggle('on', avail && S.ai);
  btn.title = avail ? 'AI 해설 표시/숨김 (a)' : '연결된 LLM이나 저장된 AI 해설이 없습니다';
}
let _pwTimer = null;
function ensurePrewarmPoll(){
  clearTimeout(_pwTimer);
  if(S.srvOk && S.prewarm && S.prewarm.active){
    _pwTimer = setTimeout(loadServerStatus, 3000);
  }
}
function updateWikiBadge(){
  const dot = $('#wikiDot'); if(!dot) return;
  const n = (S.wiki && S.wiki.doc_count) || 0;
  dot.textContent = String(n);
  dot.className = n > 0 ? 'tag ent' : 'tag';
}
async function loadServerStatus(){
  try{
    const r = await fetch('/api/status');
    if(!r.ok) return;
    const d = await r.json();
    if(d && d.ok){
      const firstInit = !S.srvOk;
      S.srvOk = true;
      S.llmCfg = d.llm || S.llmCfg;
      S.prewarm = d.prewarm || S.prewarm;
      if(d.wiki) S.wiki = d.wiki;
      if(firstInit){
        S.threads = d.threads || {};
        S.pins = d.pins || {};
        S.done = d.done || lsGet('done', []);
        S.bookmarks = d.bookmarks || lsGet('bookmarks', []);
        S.last = d.last || lsGet('last', null);
      }
      updateLlmBadge();
      updateWikiBadge();
      ensurePrewarmPoll();
      if(firstInit){
        renderSide(true);
        if(S.tutTab === 'tutor'){ S.briefKey = ''; renderChatTutor(false, false); }
      }
    }
  } catch(e){
    S.srvOk = false;
    S.done = lsGet('done', []);
    S.bookmarks = lsGet('bookmarks', []);
    S.last = lsGet('last', null);
    updateLlmBadge();
  }
}
function init(){
  $('#ttl').textContent = D.title + ' · ' + D.stats.files + '파일 ' + D.stats.funcs + '함수';
  if(lsGet('light', false)) document.documentElement.classList.add('light');
  const savedFonts = lsGet('fonts', null);
  if(savedFonts && typeof savedFonts === 'object'){
    S.fonts = {l:clampPx(savedFonts.l || 13.5), c:clampPx(savedFonts.c || 13.5), r:clampPx(savedFonts.r || 13.5)};
  } else {
    const leg = clampPx(lsGet('fontPx', 13.5));
    S.fonts = {l:leg, c:leg, r:leg};
  }
  S.fontScope = lsGet('fontScope', 'all');
  const fSel = $('#fontScope'); if(fSel){ fSel.value = S.fontScope; fSel.onchange = e => { S.fontScope = e.target.value; lsSet('fontScope', S.fontScope); syncFontUI(); }; }
  syncFontUI();
  $('#bFontDn').onclick = () => changeFont(-1, false);
  $('#bFontUp').onclick = () => changeFont(1, false);
  $('#bFontRst').onclick = () => changeFont(0, true);
  S.hideL = !!lsGet('hideL', false);
  S.hideR = !!lsGet('hideR', false);
  applyPanels();
  $('#bTogL').onclick = () => togglePanel('l');
  $('#bTogR').onclick = () => togglePanel('r');
  $('#bSpL').onclick = e => { e.stopPropagation(); togglePanel('l'); };
  $('#bSpR').onclick = e => { e.stopPropagation(); togglePanel('r'); };
  initTooltip();
  S.ai = lsGet('ai', true); updateAiBtn();
  $$('.tabs button').forEach(b => b.onclick = () => setTab(b.dataset.tab));
  $$('.sidetabs button').forEach(b => b.onclick = () => { S.sideTab = b.dataset.st; renderSide(); });
  $$('.tuttabs button').forEach(b => b.onclick = () => { S.tutTab = b.dataset.tt; renderTutor(); });
  $('#flt').oninput = e => { S.filter = e.target.value; renderSide(); };
  $('#bPal').onclick = openPalette; $('#bHelp').onclick = () => $('#help').classList.add('show');
  $('#bAi').onclick = () => { if($('#bAi').disabled) return; S.ai = !S.ai; lsSet('ai', S.ai); updateAiBtn(); renderTutor(); if(S.tab === 'ov') renderOverview(); };
  $('#bTheme').onclick = () => { document.documentElement.classList.toggle('light'); lsSet('light', document.documentElement.classList.contains('light')); if(S.tab === 'graph') renderGraph(); if(S.tab === 'ov') renderOverview(); };
  $('#bFocus').onclick = () => { S.focus = !S.focus; $('#bFocus').classList.toggle('on', S.focus); applyVisibility(); const r = rowOf(S.line); if(r) r.scrollIntoView({block: 'center'}); };
  $('#bPrev').onclick = () => stepStmt(-1); $('#bNext').onclick = () => stepStmt(1);
  ['gScope', 'gDepth', 'gDir', 'gGuess'].forEach(i => $('#' + i).onchange = () => renderGraph());
  $('#gFit').onclick = () => { const s = $('#gsvg'); if(s._fit){ Object.assign(s._view, s._fit); s.setAttribute('viewBox', [s._fit.x, s._fit.y, s._fit.w, s._fit.h].join(' ')); } };
  $('#gBack').onclick = () => graphHistMove(-1);
  $('#gFwd').onclick = () => graphHistMove(1);
  $('#gPop').onclick = openGraphWindow;
  $('#gsvg').addEventListener('mouseup', ev => { if(ev.button === 3){ ev.preventDefault(); graphHistMove(-1); } else if(ev.button === 4){ ev.preventDefault(); graphHistMove(1); } });
  $('#palIn').oninput = e => palList(e.target.value);
  $('#palIn').onkeydown = e => { if(e.key === 'Enter' && palList.top && palList.top[0]){ $('#pal').classList.remove('show'); palList.top[0].go(); } };
  $('#pal').onclick = e => { if(e.target.id === 'pal') $('#pal').classList.remove('show'); };
  $('#help').onclick = e => { if(e.target.id === 'help') $('#help').classList.remove('show'); };
  $('#ovGraphModal').onclick = e => { if(e.target.id === 'ovGraphModal') $('#ovGraphModal').classList.remove('show'); };
  $('#bOvPopClose').onclick = () => $('#ovGraphModal').classList.remove('show');
  $('#bOvPopFit').onclick = () => { const s = $('#osvgPop'); if(s._fit){ Object.assign(s._view, s._fit); s.setAttribute('viewBox', [s._fit.x, s._fit.y, s._fit.w, s._fit.h].join(' ')); } };

  // 프로젝트 선택·전환 모달
  async function loadProjectList(){
    const listEl = $('#projList'), stEl = $('#projStatus');
    if(!S.srvOk){
      stEl.textContent = '⚠ 서버 모드(--serve / run_code_tutor.bat)로 실행된 화면에서만 프로젝트 전환이 가능합니다.';
      listEl.innerHTML = '';
      return;
    }
    stEl.textContent = '목록 불러오는 중…';
    try{
      const r = await fetch('/api/projects');
      const d = await r.json();
      const projs = (d && d.projects) || [];
      stEl.textContent = projs.length ? ('저장된 프로젝트 ' + projs.length + '개 (클릭해서 전환)') : '저장된 프로젝트가 아직 없습니다.';
      listEl.innerHTML = projs.map(p => {
        const meta = [];
        if(p.qa_count) meta.push('💬 질문 ' + p.qa_count);
        if(p.pin_count) meta.push('📌 노트 ' + p.pin_count);
        if(p.bmk_count) meta.push('⭐ 북마크 ' + p.bmk_count);
        if(p.done_count) meta.push('✓ 완료 ' + p.done_count);
        const st = p.updated_at ? ('최근 ' + p.updated_at.slice(5, 16)) : '';
        return '<div class="pitem' + (p.active ? ' cur' : '') + '"><div class="pmain"><div class="pnm"><span>' + E(p.name) + '</span>' + (p.active ? '<span class="tag ent">현재 열림</span>' : '') + (!p.exists ? '<span class="tag dead">폴더 없음</span>' : '') + (meta.length ? '<span class="small muted">' + E(meta.join(' · ')) + '</span>' : '') + '</div><div class="proot" title="' + E(p.root) + '">' + E(p.root) + (st ? ' · ' + E(st) : '') + '</div></div>' + (p.exists ? ('<button data-open-proj="' + E(p.root) + '">' + (p.active ? '새로 불러오기' : '바로 열기 ▶') + '</button>') : '') + (!p.active ? '<button data-del-proj="' + E(p.ws_id) + '" title="튜터 작업 기록 삭제(원본 코드는 안전)">×</button>' : '') + '</div>';
      }).join('');
      $$('[data-open-proj]', listEl).forEach(b => b.onclick = () => switchProject(b.dataset.openProj));
      $$('[data-del-proj]', listEl).forEach(b => b.onclick = async () => {
        await apiPost('/api/project_remove', {ws_id: b.dataset.delProj});
        loadProjectList();
      });
    } catch(err){
      stEl.textContent = '목록 조회 실패: ' + String(err);
    }
  }
  async function switchProject(path){
    path = (path || '').trim(); if(!path) return;
    const stEl = $('#projStatus');
    stEl.textContent = '⏳ 프로젝트를 분석해 여는 중입니다…';
    try{
      const res = await apiPost('/api/project_switch', {path});
      if(res && res.ok && res.url){
        window.location.href = res.url;
      } else {
        stEl.textContent = '⚠ ' + ((res && res.error) || '열기에 실패했습니다.');
      }
    } catch(err){
      stEl.textContent = '⚠ 전환 실패: ' + String(err);
    }
  }
  $('#bProj').onclick = () => { $('#projModal').classList.add('show'); loadProjectList(); };
  $('#projClose').onclick = () => $('#projModal').classList.remove('show');
  $('#projModal').onclick = e => { if(e.target.id === 'projModal') $('#projModal').classList.remove('show'); };
  $('#bOpenPath').onclick = () => switchProject($('#projPathIn').value);
  $('#projPathIn').addEventListener('keydown', e => { if(e.key === 'Enter'){ e.preventDefault(); switchProject($('#projPathIn').value); } });
  $('#bBrowseProj').onclick = async () => {
    if(!S.srvOk){ $('#projStatus').textContent = '⚠ 서버 모드에서만 폴더 찾아보기가 동작합니다.'; return; }
    const btn = $('#bBrowseProj');
    btn.disabled = true;
    $('#projStatus').textContent = '폴더 선택 창을 여는 중… (창이 뒤에 숨어 있으면 작업 표시줄을 확인하세요)';
    try{
      const res = await apiPost('/api/project_browse', {});
      if(res && res.ok && res.path){
        $('#projPathIn').value = res.path;
        await switchProject(res.path);
      } else {
        $('#projStatus').textContent = res && res.error ? ('⚠ ' + res.error) : '선택이 취소되었습니다.';
      }
    } catch(err){
      $('#projStatus').textContent = '⚠ 폴더 선택 실패: ' + String(err);
    } finally {
      btn.disabled = false;
    }
  };

  // LLM 설정 모달
  $('#bLlmCfg').onclick = () => {
    $('#cfgUseLlm').checked = !!(S.llmCfg && S.llmCfg.use_llm);
    $('#cfgUrl').value = (S.llmCfg && S.llmCfg.base_url) || 'http://localhost:8000/v1';
    $('#cfgModel').value = (S.llmCfg && S.llmCfg.model) || '';
    $('#cfgKey').value = (S.llmCfg && S.llmCfg.has_key) ? '__KEEP__' : '';
    $('#cfgExtra').value = (S.llmCfg && S.llmCfg.extra_body) || '';
    $('#cfgStatus').textContent = S.srvOk ? '' : '※ 현재 정적 HTML 파일로 열려 있습니다. --serve 모드로 실행해야 실시간 LLM 연동이 가능합니다.';
    updateLlmBadge();
    $('#llmModal').classList.add('show');
  };
  $('#cfgClose').onclick = () => $('#llmModal').classList.remove('show');
  $('#llmModal').onclick = e => { if(e.target.id === 'llmModal') $('#llmModal').classList.remove('show'); };
  $('#bPrewarm').onclick = async () => {
    if(!S.srvOk){ $('#cfgStatus').textContent = '⚠ 서버 모드(--serve)에서만 사용 가능합니다.'; return; }
    try{
      const res = await apiPost('/api/prewarm', {action:'start'});
      S.prewarm = res.prewarm || S.prewarm;
      updateLlmBadge(); ensurePrewarmPoll();
      if(!res.ok && res.message) $('#cfgStatus').textContent = res.message;
    } catch(err){ $('#cfgStatus').textContent = '오류: ' + String(err); }
  };
  $('#cfgSave').onclick = async () => {
    if(!S.srvOk){ $('#cfgStatus').textContent = '⚠ 서버 모드(--serve)로 실행된 화면에서만 저장할 수 있습니다.'; return; }
    $('#cfgStatus').textContent = '연결 테스트 중…';
    try{
      const res = await apiPost('/api/config', {
        use_llm: $('#cfgUseLlm').checked,
        base_url: $('#cfgUrl').value.trim(),
        model: $('#cfgModel').value.trim(),
        api_key: $('#cfgKey').value.trim(),
        extra_body: $('#cfgExtra').value.trim(),
      });
      S.llmCfg = res.llm || S.llmCfg;
      if(res.prewarm) S.prewarm = res.prewarm;
      updateLlmBadge(); ensurePrewarmPoll();
      $('#cfgStatus').textContent = res.message || (res.connected ? '연결 성공' : '저장 완료');
      S.briefKey = '';
      if(S.tutTab === 'tutor') renderChatTutor(false, false);
    } catch(err){
      $('#cfgStatus').textContent = '오류: ' + String(err);
    }
  };

  // 논문 PDF(.pdf/.pd) · Markdown(.md) 경량 Wiki 모달
  function renderWikiModal(){
    const w = S.wiki || {auto_dirs:[], custom_sources:[], doc_count:0, total_chunks:0, docs:[]};
    $('#wikiMeta').textContent = w.doc_count ? (w.doc_count + '문서 · ' + w.total_chunks + '청크') : '문서 없음';
    const srcs = [];
    (w.auto_dirs || []).forEach(d => srcs.push('<span class="tag ent" title="프로젝트 내 자동 감지 폴더">자동: ' + E(d) + ' <button class="tbtn" data-rm-wsrc="' + E(d) + '" style="padding:0 4px;margin-left:3px" title="자동 폴더 제외">×</button></span>'));
    (w.custom_sources || []).forEach(s => srcs.push('<span class="tag">' + E(s) + ' <button class="tbtn" data-rm-wsrc="' + E(s) + '" style="padding:0 4px;margin-left:3px">×</button></span>'));
    $('#wikiSources').innerHTML = srcs.length ? ('소스: ' + srcs.join(' ')) : '<span class="muted">등록된 추가 소스 없음 (프로젝트 내 <code>papers/</code> 폴더가 있으면 자동 인식)</span>';
    $$('[data-rm-wsrc]', $('#wikiSources')).forEach(b => b.onclick = async () => {
      const res = await apiPost('/api/wiki/index', {action:'remove_source', path: b.dataset.rmWsrc});
      if(res && res.status){ S.wiki = res.status; updateWikiBadge(); renderWikiModal(); S.briefKey = ''; }
    });
    const docs = w.docs || [];
    $('#wikiDocList').innerHTML = docs.length ? docs.map(d => {
      const badge = d.summary_source === 'llm' ? '<span class="tag ent">LLM Wiki</span>' : '<span class="tag">정적 요약</span>';
      const kindTag = '<span class="tag">' + E(d.kind.toUpperCase()) + '</span>';
      const warn = d.warning ? ('<span class="small" style="color:var(--warn)" title="' + E(d.warning) + '">⚠</span>') : '';
      return '<div class="wdoc' + (S.wikiDocId === d.id ? ' on' : '') + '" data-wdoc="' + E(d.id) + '">' +
        kindTag + '<b style="flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap">' + E(d.name) + '</b>' +
        warn + '<span class="small muted">' + d.page_count + 'p · ' + d.chunk_count + '청크 (' + E(d.engine) + ')</span>' + badge + '</div>';
    }).join('') : '<div class="small muted" style="padding:8px">인덱싱된 논문/문서가 없습니다. 위에서 폴더나 파일(.pdf, .pd, .md, .txt)을 추가해 주세요.</div>';
    $$('[data-wdoc]', $('#wikiDocList')).forEach(el => el.onclick = () => loadWikiDocPreview(el.dataset.wdoc));
    updateWikiBadge();
  }
  async function loadWikiDocPreview(docId){
    S.wikiDocId = docId;
    renderWikiModal();
    const pv = $('#wikiPreview');
    pv.style.display = 'block';
    pv.innerHTML = '<span class="muted">불러오는 중…</span>';
    try{
      const r = await fetch('/api/wiki/doc?id=' + encodeURIComponent(docId));
      const d = await r.json();
      if(!d || !d.ok || !d.doc){ pv.textContent = '문서를 불러올 수 없습니다.'; return; }
      const doc = d.doc;
      let h = '<div style="display:flex;align-items:center;gap:6px;margin-bottom:6px"><b>' + E(doc.name) + '</b><span class="tag">' + E(doc.summary_source === 'llm' ? 'LLM Wiki' : '정적 요약') + '</span></div>';
      if(doc.warning) h += '<div class="small" style="color:var(--warn);margin-bottom:6px">⚠ ' + E(doc.warning) + '</div>';
      h += '<div class="md">' + mdBlock(doc.summary || '') + '</div>';
      if(doc.chunks && doc.chunks.length){
        h += '<details style="margin-top:8px"><summary class="small muted" style="cursor:pointer">추출된 원문 청크 미리보기 (' + doc.chunks.length + '/' + doc.chunk_count + ')</summary>';
        h += doc.chunks.slice(0, 6).map(c => '<div class="wiki-ref-item"><div class="small" style="color:var(--ac)">' + E(c.loc) + '</div><div class="small muted">' + E(c.text) + '</div></div>').join('');
        h += '</details>';
      }
      pv.innerHTML = h;
    } catch(err){
      pv.textContent = '미리보기 오류: ' + String(err);
    }
  }
  async function refreshWikiStatus(){
    if(!S.srvOk) return;
    try{
      const r = await fetch('/api/wiki/status');
      const d = await r.json();
      if(d && d.ok && d.wiki){ S.wiki = d.wiki; renderWikiModal(); }
    } catch(e){}
  }
  $('#bWiki').onclick = () => {
    $('#wikiStatus').textContent = S.srvOk ? '' : '⚠ 서버 모드(--serve)에서만 논문 Wiki 연동이 동작합니다.';
    $('#wikiPreview').style.display = 'none';
    renderWikiModal();
    $('#wikiModal').classList.add('show');
    refreshWikiStatus();
  };
  $('#wikiClose').onclick = () => $('#wikiModal').classList.remove('show');
  $('#wikiModal').onclick = e => { if(e.target.id === 'wikiModal') $('#wikiModal').classList.remove('show'); };
  async function runWikiAction(payload, waitMsg){
    if(!S.srvOk){ $('#wikiStatus').textContent = '⚠ 서버 모드(--serve)에서만 사용 가능합니다.'; return; }
    $('#wikiStatus').textContent = waitMsg || '처리 중…';
    try{
      const res = await apiPost('/api/wiki/index', payload);
      if(res && res.status){ S.wiki = res.status; renderWikiModal(); }
      if(res && res.cancelled){ $('#wikiStatus').textContent = '선택이 취소되었습니다.'; return; }
      if(res && res.error){ $('#wikiStatus').textContent = '⚠ ' + res.error; return; }
      if(payload.action === 'build_llm'){
        $('#wikiStatus').textContent = '✅ LLM Wiki 요약 완료: ' + (res.built || 0) + '건' + (res.errors && res.errors.length ? (' (오류 ' + res.errors.length + '건)') : '');
      } else {
        $('#wikiStatus').textContent = '✅ 인덱싱 완료 (총 ' + ((res.status && res.status.doc_count) || 0) + '문서 / ' + ((res.status && res.status.total_chunks) || 0) + '청크)';
      }
      S.briefKey = '';
      if(S.tutTab === 'tutor') renderChatTutor(false, false);
    } catch(err){
      $('#wikiStatus').textContent = '⚠ 오류: ' + String(err);
    }
  }
  $('#bWikiAddDir').onclick = () => runWikiAction({action:'browse_dir'}, '폴더 선택 창을 여는 중…');
  $('#bWikiAddFiles').onclick = () => runWikiAction({action:'browse_files'}, '파일 선택 창을 여는 중…');
  $('#bWikiAddPath').onclick = () => {
    const p = $('#wikiPathIn').value.trim();
    if(!p) return;
    $('#wikiPathIn').value = '';
    runWikiAction({action:'add_path', path:p}, '경로 추가 및 추출 중…');
  };
  $('#wikiPathIn').addEventListener('keydown', e => { if(e.key === 'Enter'){ e.preventDefault(); $('#bWikiAddPath').click(); } });
  $('#bWikiScan').onclick = () => runWikiAction({action:'scan', force:true}, '텍스트 추출 및 재인덱싱 중…');
  $('#bWikiBuildLlm').onclick = () => runWikiAction({action:'build_llm', force:false}, '✨ LLM으로 논문 Wiki 요약 카드 생성 중…');

  // 1:1 채팅 입력 컨트롤
  const sendNow = () => { const i = $('#chatIn'); const q = i.value.trim(); if(!q) return; i.value = ''; sendQuestion(q, 'chat'); };
  $('#bSendChat').onclick = sendNow;
  $('#chatIn').addEventListener('keydown', e => {
    if(e.key === 'Enter' && !e.shiftKey){ e.preventDefault(); sendNow(); }
  });
  $('#tutLevel').onchange = e => { S.level = e.target.value; S.briefKey = ''; renderChatTutor(false, false); };
  $('#bClrChat').onclick = async () => {
    const u = U[S.unit]; if(!u) return;
    if(S.srvOk){ try{ await apiPost('/api/clear_thread', {unit_id: u.id}); } catch(e){} }
    S.threads[String(u.id)] = [];
    renderChatTutor(true, false);
    toast('대화 기록을 비웠습니다');
  };

  initSplit('#sp1', '--sw', 'l'); initSplit('#sp2', '--tw', 'r');
  const code = $('#code');
  let dragStart = 0, dragEnd = 0, dragActive = false, justDragged = false;
  code.addEventListener('mousedown', e => {
    if(e.button !== 0 || e.shiftKey || e.ctrlKey || e.metaKey || e.altKey) return;
    if(e.target.closest('.fold, .sbadge, [data-c], [data-v]')) return;
    const row = e.target.closest('.ln'); if(!row) return;
    dragStart = dragEnd = +row.dataset.l;
    dragActive = true;
  });
  code.addEventListener('mousemove', e => {
    if(!dragActive) return;
    const row = e.target.closest('.ln'); if(!row) return;
    const nl = +row.dataset.l;
    if(nl === dragEnd) return;
    dragEnd = nl;
    const a = Math.min(dragStart, dragEnd), b = Math.max(dragStart, dragEnd);
    clearSelBlock();
    for(let i = a; i <= b; i++){ const r = rowOf(i); if(r){ r.classList.add('sel-block'); selBlockRows.push(r); } }
  });
  window.addEventListener('mouseup', () => {
    if(!dragActive) return;
    dragActive = false;
    if(dragStart && dragEnd && dragStart !== dragEnd){
      justDragged = true;
      try{ const sel = window.getSelection(); if(sel) sel.removeAllRanges(); } catch(e){}
      selectRange(Math.min(dragStart, dragEnd), Math.max(dragStart, dragEnd), {noscroll: true});
    }
  });
  code.addEventListener('click', e => {
    if(justDragged){ justDragged = false; return; }
    const fold = e.target.closest('.fold'); if(fold){ const id = +fold.dataset.fold; if(S.folded.has(id)) S.folded.delete(id); else S.folded.add(id); applyVisibility(); e.stopPropagation(); return; }
    const sb = e.target.closest('.sbadge'); if(sb){ selectStep(+sb.dataset.su, +sb.dataset.step); e.stopPropagation(); return; }
    const row = e.target.closest('.ln'); if(!row) return;
    const ln = +row.dataset.l;
    const c = e.target.closest('[data-c]');
    if(c && (e.ctrlKey || e.metaKey || e.altKey)){ gotoUnit(+c.dataset.c); return; }
    if(e.shiftKey && S.line){ selectRange(Math.min(S.line, ln), Math.max(S.line, ln), {noscroll: true}); return; }
    const v = e.target.closest('[data-v]'); if(v){ S.varSel = S.varSel === v.dataset.v ? null : v.dataset.v; if(S.varSel) S.tutTab = 'var'; }
    const insideSel = S.selRange && ln >= S.selRange[0] && ln <= S.selRange[1];
    selectLine(ln, {noscroll: true, keepRange: insideSel, clearRange: !insideSel});
  });
  code.addEventListener('dblclick', e => { const c = e.target.closest('[data-c]'); if(c) gotoUnit(+c.dataset.c); });
  document.addEventListener('keydown', e => {
    const tag = (document.activeElement && document.activeElement.tagName) || '';
    if((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'k'){ e.preventDefault(); openPalette(); return; }
    if(e.key === 'Escape'){ $('#pal').classList.remove('show'); $('#help').classList.remove('show'); $('#llmModal').classList.remove('show'); $('#projModal').classList.remove('show'); $('#ovGraphModal').classList.remove('show'); return; }
    if(tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT') return;
    if(e.altKey && e.key === 'ArrowLeft'){ e.preventDefault(); histMove(-1); return; }
    if(e.altKey && e.key === 'ArrowRight'){ e.preventDefault(); histMove(1); return; }
    if(e.ctrlKey || e.metaKey) return;
    if(e.key === 'Backspace' && S.tab === 'graph'){ e.preventDefault(); graphHistMove(-1); return; }
    const k = e.key;
    if(k === '1') setTab('ov'); else if(k === '2') setTab('graph'); else if(k === '3') setTab('code');
    else if(k === '?'){ $('#help').classList.add('show'); }
    else if(k === 'a'){ $('#bAi').click(); }
    else if(S.tab === 'code'){
      if(k === 'ArrowDown' || k === 'j'){ e.preventDefault(); selectLine(nextVisible(1)); }
      else if(k === 'ArrowUp' || k === 'k'){ e.preventDefault(); selectLine(nextVisible(-1)); }
      else if(k === 'n') stepStmt(1); else if(k === 'p') stepStmt(-1);
      else if(k === ']') stepUnit(1); else if(k === '[') stepUnit(-1);
      else if(k === 'f') $('#bFocus').click();
    }
  });
  window.addEventListener('resize', () => { if(S.tab === 'graph') renderGraph(); });
  const start = D.order.down.length ? U[D.order.down[0]] : U[0];
  const first = (start && start.k !== 'm') ? start : null;
  S.file = first ? first.f : 0; S.sideTab = 'files';
  renderSide(); setTab('ov');
  S.line = 1;
  loadServerStatus();
}
function nextVisible(d){ let l = S.line + d; const rows = codeRows; while(l >= 1 && l <= rows.length && rows[l-1].classList.contains('hid')) l += d; return Math.max(1, Math.min(rows.length, l)); }
init();
</script>
</body>
</html>
"""


def load_template() -> str:
    if not _EMBEDDED_TEMPLATE.startswith("@@EMBED"):
        return _EMBEDDED_TEMPLATE
    return (Path(__file__).with_name("template.html")).read_text(encoding="utf-8")


def js_json(obj: Any) -> str:
    s = json.dumps(obj, ensure_ascii=False, separators=(",", ":"))
    return s.replace("</", "<\\/").replace("<!--", "\\u003c!--")


def html_escape(s: str) -> str:
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


def build_html(data: dict, fdata: List[dict]) -> str:
    tpl = load_template()
    files_tags = "\n".join(
        f'<script type="application/json" class="fd" data-i="{i}">{js_json(fd)}</script>' for i, fd in enumerate(fdata))
    data_tag = f'<script type="application/json" id="ct-data">{js_json(data)}</script>'
    return (tpl.replace("__TITLE__", html_escape(data["title"]))
            .replace("__DATA_TAG__", data_tag).replace("__FILES_TAGS__", files_tags))


def load_config() -> Dict[str, Any]:
    cfg = {"base_url": os.getenv("OPENAI_BASE_URL", "http://localhost:8000/v1"), "model": "",
           "api_key": os.getenv("OPENAI_API_KEY", ""), "use_llm": False, "last_dir": "",
           "workers": 2, "max_calls": 150, "timeout": 90, "extra_body": "",
           "serve_mode": True, "port": 8765}
    try:
        if CONFIG_PATH.is_file():
            saved = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
            if isinstance(saved, dict):
                cfg.update(saved)
    except Exception:
        pass
    return cfg


def save_config(cfg: Dict[str, Any]) -> None:
    try:
        CONFIG_PATH.write_text(json.dumps(cfg, ensure_ascii=False, indent=2), encoding="utf-8")
        try:
            os.chmod(CONFIG_PATH, 0o600)   # API 키가 들어 있으므로 본인만 읽도록
        except OSError:
            pass
    except OSError:
        pass


def get_project_workspace_dir(root: Path, storage_root: Optional[Path] = None) -> Path:
    """원본 프로젝트 폴더를 건드리지 않고 Code Tutor 캐시·HTML을 저장할 전용 작업 폴더를 반환한다."""
    resolved = Path(root).resolve()
    base = Path(storage_root) if storage_root is not None else WORKSPACES_ROOT
    safe_name = re.sub(r'[<>:"/\\|?*\x00-\x1f]+', "_", resolved.name).strip(" .")[:60] or "project"
    norm = str(resolved).lower() if os.name == "nt" else str(resolved)
    h = hashlib.sha1(norm.encode("utf-8")).hexdigest()[:6]
    ws = base / f"{safe_name}_{h}"
    ws.mkdir(parents=True, exist_ok=True)
    legacy = resolved / ".code_tutor_cache"
    if legacy.is_dir():
        for fname in ("tutor_threads.json", "llm_tutor_cache.json", "llm_cache.json"):
            src = legacy / fname
            dst = ws / fname
            if src.is_file() and not dst.exists():
                try:
                    shutil.copy2(src, dst)
                except OSError:
                    pass
    info_path = ws / "project_info.json"
    try:
        info_path.write_text(json.dumps({
            "project_name": resolved.name,
            "project_root": str(resolved),
            "updated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        }, ensure_ascii=False, indent=2), encoding="utf-8")
    except OSError:
        pass
    return ws


def list_workspace_projects(active_root: Optional[Path] = None) -> List[dict]:
    WORKSPACES_ROOT.mkdir(parents=True, exist_ok=True)
    act_norm = ""
    if active_root is not None:
        r = Path(active_root).resolve()
        act_norm = str(r).lower() if os.name == "nt" else str(r)
    items: List[dict] = []
    for ws in WORKSPACES_ROOT.iterdir():
        if not ws.is_dir():
            continue
        info_p = ws / "project_info.json"
        if not info_p.is_file():
            continue
        try:
            info = json.loads(info_p.read_text(encoding="utf-8"))
        except Exception:
            continue
        root_str = str(info.get("project_root", "")).strip()
        if not root_str:
            continue
        root_p = Path(root_str)
        name = str(info.get("project_name") or root_p.name or ws.name)
        updated = str(info.get("updated_at", ""))
        norm = str(root_p).lower() if os.name == "nt" else str(root_p)
        html_p = next(iter(ws.glob("*_code_tutor.html")), None)
        qa_count = pin_count = done_count = bmk_count = 0
        th_p = ws / "tutor_threads.json"
        if th_p.is_file():
            try:
                td = json.loads(th_p.read_text(encoding="utf-8"))
                qa_count = sum(len([m for m in arr if m.get("role") == "user"]) for arr in (td.get("threads") or {}).values())
                pin_count = sum(len(arr) for arr in (td.get("pins") or {}).values())
                done_count = len(td.get("done") or [])
                bmk_count = len(td.get("bookmarks") or [])
            except Exception:
                pass
        items.append({
            "ws_id": ws.name,
            "name": name,
            "root": root_str,
            "updated_at": updated,
            "exists": root_p.is_dir(),
            "has_html": bool(html_p and html_p.is_file()),
            "active": bool(act_norm and norm == act_norm),
            "qa_count": qa_count,
            "pin_count": pin_count,
            "done_count": done_count,
            "bmk_count": bmk_count,
        })
    items.sort(key=lambda x: x["updated_at"], reverse=True)
    items.sort(key=lambda x: 0 if x["active"] else 1)
    return items


def _pick_directory_dialog(initial_dir: str = "", title: str = "분석할 프로젝트 폴더 선택") -> str:
    import base64
    init_b64 = base64.b64encode((initial_dir or "").encode("utf-8")).decode("ascii")
    title_b64 = base64.b64encode((title or "폴더 선택").encode("utf-8")).decode("ascii")
    code = (
        "import sys, json, base64, tkinter as tk; from tkinter import filedialog; "
        "ini = base64.b64decode(sys.argv[1]).decode('utf-8', 'replace') if len(sys.argv) > 1 and sys.argv[1] else ''; "
        "ttl = base64.b64decode(sys.argv[2]).decode('utf-8', 'replace') if len(sys.argv) > 2 and sys.argv[2] else '폴더 선택'; "
        "r = tk.Tk(); r.overrideredirect(True); r.geometry('1x1+100+100'); "
        "r.attributes('-alpha', 0.0); r.attributes('-topmost', True); r.lift(); r.focus_force(); r.update(); "
        "d = filedialog.askdirectory(parent=r, title=ttl, initialdir=(ini or None)); "
        "r.destroy(); print(json.dumps({'path': d or ''}, ensure_ascii=True))"
    )
    kw: Dict[str, Any] = {"stdin": subprocess.DEVNULL, "capture_output": True, "text": True, "encoding": "ascii", "errors": "replace", "timeout": 300}
    if os.name == "nt" and hasattr(subprocess, "CREATE_NO_WINDOW"):
        kw["creationflags"] = subprocess.CREATE_NO_WINDOW
    try:
        res = subprocess.run([sys.executable, "-c", code, init_b64, title_b64], **kw)
        out = (res.stdout or "").strip()
        if out.startswith("{"):
            return str(json.loads(out).get("path", "")).strip()
        return out
    except Exception:
        return ""


def _pick_paper_files_dialog(initial_dir: str = "") -> List[str]:
    import base64
    init_b64 = base64.b64encode((initial_dir or "").encode("utf-8")).decode("ascii")
    code = (
        "import sys, json, base64, tkinter as tk; from tkinter import filedialog; "
        "ini = base64.b64decode(sys.argv[1]).decode('utf-8', 'replace') if len(sys.argv) > 1 and sys.argv[1] else ''; "
        "r = tk.Tk(); r.overrideredirect(True); r.geometry('1x1+100+100'); "
        "r.attributes('-alpha', 0.0); r.attributes('-topmost', True); r.lift(); r.focus_force(); r.update(); "
        "fs = filedialog.askopenfilenames(parent=r, title='논문/참고 문서 선택 (.pdf, .pd, .md, .txt)', "
        "initialdir=(ini or None), "
        "filetypes=[('논문 및 마크다운', '*.pdf *.pd *.md *.markdown *.txt'), ('PDF 파일', '*.pdf *.pd'), ('마크다운/텍스트', '*.md *.markdown *.txt'), ('모든 파일', '*.*')]); "
        "r.destroy(); print(json.dumps({'paths': list(fs) if fs else []}, ensure_ascii=True))"
    )
    kw: Dict[str, Any] = {"stdin": subprocess.DEVNULL, "capture_output": True, "text": True, "encoding": "ascii", "errors": "replace", "timeout": 300}
    if os.name == "nt" and hasattr(subprocess, "CREATE_NO_WINDOW"):
        kw["creationflags"] = subprocess.CREATE_NO_WINDOW
    try:
        res = subprocess.run([sys.executable, "-c", code, init_b64], **kw)
        out = (res.stdout or "").strip()
        if out.startswith("{"):
            ps = json.loads(out).get("paths", [])
            return [str(p).strip() for p in ps if str(p).strip()]
        return []
    except Exception:
        return []


def _self_code_hash() -> str:
    try:
        return hashlib.sha1(Path(__file__).read_bytes()).hexdigest()[:12]
    except Exception:
        return VERSION


# ═════════════════════════════════════════════════════════════════════════════
#  1:1 대화형 튜터 엔진 & 로컬 웹 서버 (표준 라이브러리만 사용)
# ═════════════════════════════════════════════════════════════════════════════
TUTOR_SYS_PROMPT = (
    "너는 프로그래밍 초보자를 1:1로 가르치는 친절한 한국어 코드 튜터다. "
    "코드를 한 줄씩 기계적으로 번역하지 말고, 여러 줄이 모여 이루는 '의도(Why)', '데이터 흐름', '실제 예시 값 변화'를 설명하라. "
    "제공된 [코드]와 [AST/정적 맥락 사실]에 없는 식별자·동작은 절대 지어내지 마라. "
    "마크다운 **굵게**, `코드`, 불릿 목록(-)은 깔끔하게 사용해도 되며, "
    "LaTeX 수식 기호($\\rightarrow$ 등)는 절대 쓰지 말고 유니코드 화살표(→)와 백틱(`코드`)만 사용하라."
)


# ─────────────────────────────────────────────────────────────────────────────
#  경량 논문 PDF(.pdf / .pd) · Markdown(.md) 파서 & LLM-Wiki 인덱스
# ─────────────────────────────────────────────────────────────────────────────
PAPER_PDF_EXTS = {".pdf", ".pd"}
PAPER_TEXT_EXTS = {".md", ".markdown", ".txt"}
PAPER_ALL_EXTS = PAPER_PDF_EXTS | PAPER_TEXT_EXTS
PAPER_DEFAULT_DIRS = ("papers", "paper", "docs/papers", "doc/papers")
_WIKI_STOPWORDS = {
    "the", "and", "for", "with", "that", "this", "from", "are", "was", "were",
    "have", "has", "had", "not", "but", "can", "will", "into", "such", "when",
    "where", "which", "while", "each", "also", "more", "than", "then", "only",
    "used", "using", "based", "between", "through", "about", "after", "before",
    "self", "none", "true", "false", "return", "def", "class", "import", "end",
    "function", "else", "elif", "for", "while", "있는", "하는", "되는", "대한",
    "통해", "위해", "경우", "사용", "함수", "변수", "코드", "설명",
}


def _wiki_tokenize(text: str) -> List[str]:
    """코드 식별자(camelCase/snake_case 포함)와 한국어/영문 단어를 검색 토큰으로 분해한다."""
    if not text:
        return []
    out: List[str] = []
    seen_pos: List[str] = []
    for raw in re.findall(r"[A-Za-z_][A-Za-z0-9_]*|[가-힣]{2,}|\d+(?:\.\d+)?", text):
        low = raw.lower()
        if len(low) >= 2 and low not in _WIKI_STOPWORDS:
            seen_pos.append(low)
        if "_" in raw or any(c.isupper() for c in raw[1:]):
            for part in raw.split("_"):
                if not part:
                    continue
                subs = re.findall(r"[A-Z]+(?=[A-Z][a-z]|\d|$)|[A-Z]?[a-z]+|\d+", part)
                for sp in subs:
                    spl = sp.lower()
                    if len(spl) >= 2 and spl not in _WIKI_STOPWORDS:
                        seen_pos.append(spl)
    for tok in seen_pos:
        out.append(tok)
    return out


def _clean_paper_text(s: str) -> str:
    s = s.replace("\x00", " ").replace("\r\n", "\n").replace("\r", "\n")
    s = re.sub(r"<!--\s*Start of picture text\s*-->.*?<!--\s*End of picture text\s*-->", "", s, flags=re.S | re.I)
    s = re.sub(r"<!--\s*(?:Start|End) of picture text\s*-->", "", s, flags=re.I)
    s = re.sub(r"<br\s*/?>", " ", s, flags=re.I)
    s = re.sub(r"\u00ad\s*", "", s)
    s = re.sub(r"(\w)-\n(\w)", r"\1\2", s)
    # PDF 특수 수식 폰트(Symbol/MT Extra)에서 흔히 깨지는 기호 정리
    s = s.replace("ð", "(").replace("Þ", ")")
    s = re.sub(r"\s*¼\s*", " = ", s)
    s = re.sub(r"\(\s+\)", "()", s)
    for pua, rep in (("\uf0b4", "×"), ("\uf02d", "-"), ("\uf03d", "="), ("\uf0b1", "±"),
                     ("\uf0a3", "≤"), ("\uf0b3", "≥"), ("\uf0b9", "≠"), ("\uf0ae", "→")):
        s = s.replace(pua, rep)
    s = re.sub(r"[ \t]+", " ", s)
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


def _parse_pdf_tounicode_cmap(data: bytes) -> Dict[int, str]:
    cmap: Dict[int, str] = {}
    if b"beginbfchar" not in data and b"beginbfrange" not in data:
        return cmap
    txt = data.decode("latin-1", "replace")

    def _hex_to_str(hx: str) -> str:
        hx = re.sub(r"\s+", "", hx)
        if not hx:
            return ""
        if len(hx) % 2 == 1:
            hx = "0" + hx
        try:
            b = bytes.fromhex(hx)
            if len(b) >= 2 and len(b) % 2 == 0:
                return b.decode("utf-16-be", "replace")
            return b.decode("latin-1", "replace")
        except Exception:
            return ""

    for blk in re.findall(r"beginbfchar\s*(.*?)\s*endbfchar", txt, re.S):
        for src_h, dst_h in re.findall(r"<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>", blk):
            try:
                cmap[int(src_h, 16)] = _hex_to_str(dst_h)
            except ValueError:
                pass
    for blk in re.findall(r"beginbfrange\s*(.*?)\s*endbfrange", txt, re.S):
        for lo_h, hi_h, dst_h in re.findall(r"<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>\s*<([0-9A-Fa-f]+)>", blk):
            try:
                lo, hi = int(lo_h, 16), int(hi_h, 16)
                base_val = int(dst_h, 16)
                if hi - lo <= 512:
                    for off in range(hi - lo + 1):
                        val_bytes = (base_val + off).to_bytes(max(2, len(dst_h) // 2), "big")
                        cmap[lo + off] = val_bytes.decode("utf-16-be", "replace")
            except Exception:
                pass
    return cmap


def _decode_pdf_literal(raw_b: bytes) -> str:
    out = bytearray()
    i = 0
    n = len(raw_b)
    while i < n:
        c = raw_b[i]
        if c == 92 and i + 1 < n:  # backslash
            nxt = raw_b[i + 1]
            esc_map = {ord("n"): 10, ord("r"): 13, ord("t"): 9, ord("b"): 8, ord("f"): 12,
                       ord("("): 40, ord(")"): 41, 92: 92}
            if nxt in esc_map:
                out.append(esc_map[nxt])
                i += 2
                continue
            if 48 <= nxt <= 55:
                oct_digits = raw_b[i + 1:i + 4]
                m = re.match(rb"[0-7]{1,3}", oct_digits)
                if m:
                    out.append(int(m.group(0), 8) & 0xFF)
                    i += 1 + len(m.group(0))
                    continue
            if nxt in (10, 13):
                i += 2
                continue
        out.append(c)
        i += 1
    b = bytes(out)
    if b.startswith(b"\xfe\xff"):
        return b[2:].decode("utf-16-be", "replace")
    return b.decode("cp1252", "replace")


def _decode_pdf_hex(hx_b: bytes, cmap: Dict[int, str]) -> str:
    hx = re.sub(rb"\s+", b"", hx_b).decode("ascii", "ignore")
    if not hx:
        return ""
    if len(hx) % 2 == 1:
        hx += "0"
    try:
        b = bytes.fromhex(hx)
    except ValueError:
        return ""
    if b.startswith(b"\xfe\xff"):
        return b[2:].decode("utf-16-be", "replace")
    if cmap:
        if len(b) % 2 == 0:
            chars = []
            hit = 0
            for j in range(0, len(b), 2):
                code = (b[j] << 8) | b[j + 1]
                if code in cmap:
                    chars.append(cmap[code])
                    hit += 1
                elif 32 <= code <= 126:
                    chars.append(chr(code))
            if hit > 0:
                return "".join(chars)
        chars1 = []
        hit1 = 0
        for byte_v in b:
            if byte_v in cmap:
                chars1.append(cmap[byte_v])
                hit1 += 1
            elif 32 <= byte_v <= 126:
                chars1.append(chr(byte_v))
        if hit1 > 0:
            return "".join(chars1)
    return b.decode("latin-1", "replace")


def _extract_pdf_stdlib(raw: bytes) -> Tuple[List[Tuple[str, str]], str]:
    """외부 PDF 라이브러리 없이 표준 라이브러리(zlib+정규식)만으로 PDF 텍스트를 추출한다."""
    if b"%PDF-" not in raw[:1024]:
        return [], "올바른 PDF 헤더(%PDF-)가 없습니다."
    streams: List[bytes] = []
    for m in re.finditer(rb"stream\r?\n(.*?)\r?\n?endstream", raw, re.S):
        chunk = m.group(1)
        dec = None
        for wbits in (zlib.MAX_WBITS, -zlib.MAX_WBITS):
            try:
                dec = zlib.decompress(chunk, wbits)
                break
            except Exception:
                pass
        streams.append(dec if dec is not None else chunk)

    cmap: Dict[int, str] = {}
    for st in streams:
        if b"beginbfchar" in st or b"beginbfrange" in st:
            cmap.update(_parse_pdf_tounicode_cmap(st))

    pages_text: List[str] = []
    for st in streams:
        if b"BT" not in st or (b"Tj" not in st and b"TJ" not in st):
            continue
        frags: List[str] = []
        for bt in re.findall(rb"BT\b(.*?)\bET", st, re.S):
            pos = 0
            n = len(bt)
            line_buf: List[str] = []
            while pos < n:
                ch = bt[pos:pos + 1]
                if ch == b"(":
                    depth = 1
                    j = pos + 1
                    while j < n and depth > 0:
                        if bt[j] == 92:
                            j += 2
                            continue
                        if bt[j] == 40:
                            depth += 1
                        elif bt[j] == 41:
                            depth -= 1
                        j += 1
                    lit = _decode_pdf_literal(bt[pos + 1:max(pos + 1, j - 1)])
                    if lit:
                        line_buf.append(lit)
                    pos = j
                elif ch == b"<" and bt[pos + 1:pos + 2] != b"<":
                    end_h = bt.find(b">", pos + 1)
                    if end_h != -1:
                        hx_s = _decode_pdf_hex(bt[pos + 1:end_h], cmap)
                        if hx_s:
                            line_buf.append(hx_s)
                        pos = end_h + 1
                    else:
                        pos += 1
                elif bt[pos:pos + 2] in (b"T*", b"Td", b"TD", b"Tm"):
                    if line_buf:
                        frags.append("".join(line_buf))
                        line_buf = []
                    pos += 2
                else:
                    pos += 1
            if line_buf:
                frags.append("".join(line_buf))
        joined = _clean_paper_text("\n".join(frags))
        if len(joined) >= 20:
            printable = sum(1 for c in joined if c.isprintable() or c in "\n\t")
            if printable / max(1, len(joined)) > 0.75:
                pages_text.append(joined)

    if not pages_text:
        return [], "표준 라이브러리로 텍스트를 추출하지 못했습니다(스캔본·암호화·특수 폰트 인코딩). pypdf/pymupdf 설치 또는 .md 변환본을 권장합니다."
    return [(f"p.{i + 1}", t) for i, t in enumerate(pages_text)], ""


def _is_noise_pdf_block(txt: str, y0: float = 0.0, y1: float = 0.0, ph: float = 0.0) -> bool:
    """그림 축 눈금·범례 라벨·머리글/바닥글·목차 점선 등 비서술 노이즈 블록을 판별한다."""
    t = txt.strip()
    if not t:
        return True
    if ph > 0 and (y1 < ph * 0.055 or y0 > ph * 0.945) and len(t) < 160:
        if not re.search(r"(?:[A-Za-z가-힣]+\s+){6,}[.!?。]$", t):
            return True
    if re.search(r"\.{5,}\s*\d+\s*$", t, re.M):
        return True
    lns = [ln.strip() for ln in t.splitlines() if ln.strip()]
    has_sentence = bool(re.search(r"(?:[A-Za-z가-힣]{2,}\s+){5,}[A-Za-z가-힣0-9)]+[.!?。]", t))
    if len(lns) >= 3 and (sum(len(ln) for ln in lns) / len(lns)) < 18 and not has_sentence:
        return True
    non_sp = sum(1 for c in t if not c.isspace())
    alpha = sum(1 for c in t if c.isalpha())
    if non_sp >= 15 and (alpha / non_sp) < 0.30 and len(t) < 240 and not has_sentence:
        return True
    return False


def _prose_quality_factor(txt: str) -> float:
    """온전한 서술 문장 비율에 따라 검색 점수 가중치를 산정한다."""
    if not txt:
        return 0.6
    if len(re.findall(r"(?:^|\n|\s)\[\d{1,3}\]\s+[A-Z]", txt)) >= 2:
        return 0.45
    sents = re.findall(r"[A-Za-z가-힣]{2,}(?:\s+[A-Za-z가-힣0-9_,()'\"-]+){4,}[.!?。]", txt)
    if len(sents) >= 2:
        return 1.20
    if len(sents) == 1:
        return 1.05
    return 0.55


def _extract_pdf_pages(path: Path) -> Tuple[List[Tuple[str, str]], str, str]:
    """PDF(.pdf / .pd)에서 페이지별 텍스트를 추출한다. (pymupdf4llm → pymupdf blocks → pypdf → pdfplumber → pdftotext → stdlib)"""
    try:
        raw = path.read_bytes()
    except OSError as e:
        return [], "error", f"파일 읽기 실패: {e}"

    for mod_name in ("pymupdf", "fitz"):
        try:
            mupdf = __import__(mod_name)
            doc = mupdf.open(stream=raw, filetype="pdf")
            try:
                p4l = __import__("pymupdf4llm")
                md_pages = p4l.to_markdown(doc, page_chunks=True, show_progress=False)
                pages_md: List[Tuple[str, str]] = []
                for idx, mp in enumerate(md_pages):
                    raw_md = (mp.get("text") or "") if isinstance(mp, dict) else ""
                    kept_paras = [p for p in re.split(r"\n\s*\n", raw_md) if not _is_noise_pdf_block(p)]
                    txt = _clean_paper_text("\n\n".join(kept_paras))
                    if txt:
                        pno = ((mp.get("metadata") or {}).get("page") if isinstance(mp, dict) else None) or (idx + 1)
                        pages_md.append((f"p.{pno}", txt))
                if pages_md:
                    return pages_md, "pymupdf4llm", ""
            except ImportError:
                pass
            except Exception:
                pass

            pages: List[Tuple[str, str]] = []
            for idx, pg in enumerate(doc):
                ph = float(pg.rect.height or 0.0)
                blocks = pg.get_text("blocks") or []
                kept: List[str] = []
                for b in blocks:
                    if len(b) >= 7 and b[6] != 0:
                        continue
                    btxt = str(b[4] or "").strip()
                    if not btxt:
                        continue
                    if _is_noise_pdf_block(btxt, float(b[1]), float(b[3]), ph):
                        continue
                    kept.append(btxt)
                txt = _clean_paper_text("\n\n".join(kept))
                if txt:
                    pages.append((f"p.{idx + 1}", txt))
            if pages:
                return pages, "pymupdf", ""
        except ImportError:
            pass
        except Exception:
            pass

    for mod_name in ("pypdf", "PyPDF2"):
        try:
            mod = __import__(mod_name)
            reader = mod.PdfReader(io.BytesIO(raw))
            pages = []
            for idx, pg in enumerate(reader.pages):
                txt = _clean_paper_text(pg.extract_text() or "")
                if txt:
                    pages.append((f"p.{idx + 1}", txt))
            if pages:
                return pages, mod_name, ""
        except ImportError:
            pass
        except Exception:
            pass

    try:
        pdfplumber = __import__("pdfplumber")
        with pdfplumber.open(io.BytesIO(raw)) as pdf:
            pages = []
            for idx, pg in enumerate(pdf.pages):
                txt = _clean_paper_text(pg.extract_text() or "")
                if txt:
                    pages.append((f"p.{idx + 1}", txt))
            if pages:
                return pages, "pdfplumber", ""
    except ImportError:
        pass
    except Exception:
        pass

    pdftotext = shutil.which("pdftotext")
    if pdftotext:
        try:
            kw: Dict[str, Any] = {"input": raw, "capture_output": True, "timeout": 30}
            if os.name == "nt" and hasattr(subprocess, "CREATE_NO_WINDOW"):
                kw["creationflags"] = subprocess.CREATE_NO_WINDOW
            res = subprocess.run([pdftotext, "-enc", "UTF-8", "-", "-"], **kw)
            if res.returncode == 0 and res.stdout:
                txt_all = res.stdout.decode("utf-8", "replace")
                raw_pages = txt_all.split("\x0c")
                pages = [(f"p.{i + 1}", _clean_paper_text(p)) for i, p in enumerate(raw_pages) if _clean_paper_text(p)]
                if pages:
                    return pages, "pdftotext", ""
        except Exception:
            pass

    pages, warn = _extract_pdf_stdlib(raw)
    return pages, "stdlib", warn


def _extract_md_sections(path: Path) -> Tuple[List[Tuple[str, str]], str, str]:
    raw_bytes = path.read_bytes()
    text = ""
    for enc in ("utf-8-sig", "utf-8", "cp949", "latin-1"):
        try:
            text = raw_bytes.decode(enc)
            break
        except UnicodeDecodeError:
            continue
    text = _clean_paper_text(text)
    if not text:
        return [], "markdown", "파일 내용이 비어 있습니다."
    sections: List[Tuple[str, str]] = []
    cur_loc = "서론"
    cur_lines: List[str] = []
    for ln in text.splitlines():
        m = re.match(r"^(#{1,4})\s+(.+?)\s*$", ln)
        if m:
            body = "\n".join(cur_lines).strip()
            if body:
                sections.append((cur_loc, body))
            cur_loc = "§" + short(m.group(2).strip("# ").strip(), 40)
            cur_lines = [ln]
        else:
            cur_lines.append(ln)
    tail = "\n".join(cur_lines).strip()
    if tail:
        sections.append((cur_loc, tail))
    return sections or [("본문", text)], "markdown", ""


def _split_sentences_clean(text: str) -> List[str]:
    """문장 경계(., !, ?) 기준으로 텍스트를 온전한 문장 단위로 분할한다."""
    norm = re.sub(r"\n(?![-*•#]|\d+[.)]\s)", " ", text.strip())
    norm = re.sub(r"[ \t]+", " ", norm)
    sents = [s.strip() for s in re.split(r"(?<=[.!?。])\s+|\n+", norm) if s.strip()]
    return sents or ([norm.strip()] if norm.strip() else [])


def _chunk_sections(sections: List[Tuple[str, str]], max_chars: int = 760) -> List[Dict[str, Any]]:
    chunks: List[Dict[str, Any]] = []
    for loc, body in sections:
        paras = [p.strip() for p in re.split(r"\n\s*\n", body) if p.strip()]
        buf = ""
        for p in paras:
            if len(p) > max_chars:
                if buf:
                    chunks.append({"loc": loc, "text": buf})
                    buf = ""
                sbuf = ""
                for sent in _split_sentences_clean(p):
                    if not sbuf:
                        sbuf = sent
                    elif len(sbuf) + 1 + len(sent) <= max_chars:
                        sbuf = sbuf + " " + sent
                    else:
                        chunks.append({"loc": loc, "text": sbuf})
                        sbuf = sent
                if sbuf:
                    chunks.append({"loc": loc, "text": sbuf})
            elif not buf:
                buf = p
            elif len(buf) + 2 + len(p) <= max_chars:
                buf = buf + "\n\n" + p
            else:
                chunks.append({"loc": loc, "text": buf})
                buf = p
        if buf:
            chunks.append({"loc": loc, "text": buf})
    return chunks


class PaperWikiManager:
    """프로젝트별 논문(.pdf/.pd/.md/.txt) 텍스트 추출·경량 Wiki 요약·고속 키워드 검색기."""

    def __init__(self, proj_root: Path, cache_dir: Path):
        self.proj_root = Path(proj_root).resolve()
        self.cache_dir = Path(cache_dir)
        self.wiki_path = self.cache_dir / "paper_wiki.json"
        self.lock = threading.Lock()
        self.custom_sources: List[str] = []
        self.ignore_auto_dirs: bool = False
        self.docs: Dict[str, Dict[str, Any]] = {}
        self.df: Dict[str, int] = {}
        self.total_chunks: int = 0
        self.wiki_hash: str = "empty"
        self._load()
        if not self.docs and self._auto_dirs():
            self.scan(force=False)

    def _auto_dirs(self) -> List[Path]:
        if self.ignore_auto_dirs:
            return []
        found: List[Path] = []
        for sub in PAPER_DEFAULT_DIRS:
            p = self.proj_root / sub
            if p.is_dir():
                found.append(p.resolve())
        return found

    def _load(self) -> None:
        try:
            if self.wiki_path.is_file():
                d = json.loads(self.wiki_path.read_text(encoding="utf-8"))
                if isinstance(d, dict):
                    self.custom_sources = [str(x) for x in (d.get("custom_sources") or []) if str(x).strip()]
                    self.ignore_auto_dirs = bool(d.get("ignore_auto_dirs", False))
                    docs = d.get("docs") or {}
                    if isinstance(docs, dict):
                        self.docs = docs
        except Exception:
            self.docs = {}
        self._rebuild_stats()

    def _save(self) -> None:
        try:
            self.cache_dir.mkdir(parents=True, exist_ok=True)
            tmp = self.wiki_path.with_suffix(".tmp")
            payload = {
                "custom_sources": self.custom_sources,
                "ignore_auto_dirs": self.ignore_auto_dirs,
                "docs": self.docs,
                "updated_at": time.strftime("%Y-%m-%d %H:%M:%S"),
            }
            tmp.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
            os.replace(tmp, self.wiki_path)
        except OSError:
            pass

    def _rebuild_stats(self) -> None:
        df: Dict[str, int] = defaultdict(int)
        total = 0
        h_parts: List[str] = []
        for did in sorted(self.docs.keys()):
            doc = self.docs[did]
            h_parts.append(f"{did}:{doc.get('mtime_ns', 0)}:{doc.get('summary_source', '')}")
            for ch in doc.get("chunks") or []:
                total += 1
                for tok in set(ch.get("tokens") or []):
                    df[tok] += 1
        self.df = dict(df)
        self.total_chunks = total
        self.wiki_hash = sha1("|".join(h_parts))[:10] if h_parts else "empty"

    def _collect_source_files(self) -> List[Path]:
        files: List[Path] = []
        seen: set = set()

        def _add_file(fp: Path) -> None:
            if not fp.is_file() or fp.suffix.lower() not in PAPER_ALL_EXTS:
                return
            key = str(fp.resolve()).lower() if os.name == "nt" else str(fp.resolve())
            if key not in seen:
                seen.add(key)
                files.append(fp.resolve())

        for d in self._auto_dirs():
            for fp in sorted(d.rglob("*")):
                _add_file(fp)
        for src in self.custom_sources:
            p = Path(src)
            if p.is_file():
                _add_file(p)
            elif p.is_dir():
                for fp in sorted(p.rglob("*")):
                    _add_file(fp)
        return files

    def _static_doc_summary(self, name: str, pages: List[Tuple[str, str]]) -> str:
        locs = [loc for loc, _ in pages[:10]]
        preview = "\n\n".join(short(txt, 260) for _, txt in pages[:2])
        lines = [f"**문서:** `{name}` ({len(pages)}개 섹션/페이지)"]
        if locs:
            lines.append("**목차/위치:** " + ", ".join(locs))
        if preview:
            lines.append("**핵심 발췌:**\n" + preview)
        return "\n".join(lines)

    def scan(self, force: bool = False) -> Dict[str, Any]:
        files = self._collect_source_files()
        new_docs: Dict[str, Dict[str, Any]] = {}
        added = updated = skipped = 0
        with self.lock:
            old_docs = dict(self.docs)

        for fp in files:
            try:
                st = fp.stat()
            except OSError:
                continue
            norm = str(fp).lower() if os.name == "nt" else str(fp)
            did = sha1(norm)[:10]
            prev = old_docs.get(did)
            if not force and prev and prev.get("mtime_ns") == st.st_mtime_ns and prev.get("size") == st.st_size and prev.get("chunk_ver", 1) >= 5:
                new_docs[did] = prev
                skipped += 1
                continue

            ext = fp.suffix.lower()
            if ext in PAPER_PDF_EXTS:
                pages, engine, warn = _extract_pdf_pages(fp)
                kind = "pd" if ext == ".pd" else "pdf"
            else:
                pages, engine, warn = _extract_md_sections(fp)
                kind = "md"

            raw_chunks = _chunk_sections(pages)
            chunks: List[Dict[str, Any]] = []
            for idx, ch in enumerate(raw_chunks):
                toks = _wiki_tokenize(ch["text"])
                chunks.append({
                    "id": f"{did}_{idx}",
                    "loc": ch["loc"],
                    "text": ch["text"],
                    "tokens": toks,
                })
            summary = self._static_doc_summary(fp.name, pages)
            new_docs[did] = {
                "id": did,
                "name": fp.name,
                "path": str(fp),
                "kind": kind,
                "size": st.st_size,
                "mtime_ns": st.st_mtime_ns,
                "engine": engine,
                "warning": warn,
                "page_count": len(pages),
                "chunk_count": len(chunks),
                "summary": summary,
                "summary_tokens": _wiki_tokenize(fp.name + " " + summary),
                "summary_source": "static",
                "chunk_ver": 5,
                "chunks": chunks,
            }
            if prev:
                updated += 1
            else:
                added += 1

        with self.lock:
            self.docs = new_docs
            self._rebuild_stats()
            self._save()
        return {
            "ok": True,
            "added": added,
            "updated": updated,
            "skipped": skipped,
            "status": self.status(),
        }

    def build_llm_wiki(self, client: LLMClient, force: bool = False) -> Dict[str, Any]:
        self.scan(force=False)
        with self.lock:
            target_ids = [
                did for did, doc in self.docs.items()
                if doc.get("chunks") and (force or doc.get("summary_source") != "llm")
            ]
        built = 0
        errors: List[str] = []
        for did in target_ids:
            with self.lock:
                doc = self.docs.get(did)
                if not doc:
                    continue
                sample_txt = "\n\n".join(
                    f"[{ch['loc']}]\n{ch['text']}" for ch in (doc.get("chunks") or [])[:10]
                )[:4500]
                doc_name = doc["name"]
            prompt = (
                f"다음은 프로젝트와 관련된 참고 논문/문서 `{doc_name}`의 발췌 본문이다.\n"
                "코드를 설명할 때 참고할 수 있도록 **경량 LLM-Wiki 요약 카드**를 한국어로 간결하게 정리하라.\n"
                "[출력 형식]\n"
                "- **핵심 주제/알고리즘:** (2~3문장)\n"
                "- **주요 수식·기호·변수 매핑:** (본문에 나온 기호/변수의 물리적·수학적 의미 목록)\n"
                "- **좌표계·가정·제약:** (본문에 명시된 가정/조건, 없으면 생략)\n"
                "LaTeX 수식 기호($ 등)는 쓰지 말고 유니코드/백틱(`x_k`)만 사용하라. 본문에 없는 내용은 지어내지 마라.\n\n"
                f"[문서 발췌]\n{sample_txt}"
            )
            try:
                raw, _ = client.complete_messages(
                    [{"role": "system", "content": "너는 기술 논문과 알고리즘 문서를 코드 학습용 Wiki 카드로 정확하게 요약하는 연구 보조자다."},
                     {"role": "user", "content": prompt}],
                    max_tokens=700, temperature=0.15,
                )
                txt = clean_llm_text(raw, keep_md=True)
                if txt:
                    with self.lock:
                        if did in self.docs:
                            self.docs[did]["summary"] = txt
                            self.docs[did]["summary_source"] = "llm"
                            self.docs[did]["summary_tokens"] = _wiki_tokenize(doc_name + " " + txt)
                            self._rebuild_stats()
                            self._save()
                            built += 1
            except Exception as e:
                errors.append(f"{doc_name}: {e}")
        return {"ok": True, "built": built, "errors": errors, "status": self.status()}

    def add_sources(self, paths: List[str]) -> Dict[str, Any]:
        changed = False
        with self.lock:
            existing = {s.lower() if os.name == "nt" else s for s in self.custom_sources}
            for raw in paths:
                p = Path(str(raw).strip().strip('"'))
                if not p.exists():
                    continue
                ps = str(p.resolve())
                key = ps.lower() if os.name == "nt" else ps
                if key not in existing:
                    self.custom_sources.append(ps)
                    existing.add(key)
                    changed = True
            if changed:
                self._save()
        return self.scan(force=False)

    def remove_source(self, path_str: str) -> Dict[str, Any]:
        target_key = path_str.lower() if os.name == "nt" else path_str
        with self.lock:
            self.custom_sources = [
                s for s in self.custom_sources
                if (s.lower() if os.name == "nt" else s) != target_key
            ]
            for sub in PAPER_DEFAULT_DIRS:
                p = (self.proj_root / sub)
                if p.is_dir():
                    pk = str(p.resolve()).lower() if os.name == "nt" else str(p.resolve())
                    if pk == target_key:
                        self.ignore_auto_dirs = True
            self._save()
        return self.scan(force=False)

    def get_doc(self, doc_id: str) -> Optional[Dict[str, Any]]:
        with self.lock:
            doc = self.docs.get(doc_id)
            if not doc:
                return None
            return {
                "id": doc["id"],
                "name": doc["name"],
                "path": doc["path"],
                "kind": doc["kind"],
                "engine": doc.get("engine", ""),
                "warning": doc.get("warning", ""),
                "page_count": doc.get("page_count", 0),
                "chunk_count": doc.get("chunk_count", 0),
                "summary": doc.get("summary", ""),
                "summary_source": doc.get("summary_source", "static"),
                "chunks": [{"loc": c["loc"], "text": c["text"]} for c in (doc.get("chunks") or [])[:25]],
            }

    def status(self) -> Dict[str, Any]:
        with self.lock:
            docs_meta = []
            for doc in self.docs.values():
                docs_meta.append({
                    "id": doc["id"],
                    "name": doc["name"],
                    "path": doc["path"],
                    "kind": doc["kind"],
                    "engine": doc.get("engine", ""),
                    "warning": doc.get("warning", ""),
                    "page_count": doc.get("page_count", 0),
                    "chunk_count": doc.get("chunk_count", 0),
                    "summary_source": doc.get("summary_source", "static"),
                })
            docs_meta.sort(key=lambda x: x["name"].lower())
            return {
                "auto_dirs": [str(p) for p in self._auto_dirs()],
                "custom_sources": list(self.custom_sources),
                "doc_count": len(docs_meta),
                "total_chunks": self.total_chunks,
                "wiki_hash": self.wiki_hash,
                "docs": docs_meta,
            }

    def search(self, query_text: str, extra_tokens: Optional[List[str]] = None,
               top_k: int = 8, max_chars: int = 8000, per_doc_limit: int = 2) -> List[Dict[str, Any]]:
        with self.lock:
            if not self.docs or self.total_chunks == 0:
                return []
            q_toks = _wiki_tokenize(query_text)
            if extra_tokens:
                for et in extra_tokens:
                    q_toks.extend(_wiki_tokenize(et))
            if not q_toks:
                return []
            q_freq = Counter(q_toks)
            n_docs = max(1, self.total_chunks)
            df = self.df

            candidates: List[Tuple[float, Dict[str, Any]]] = []
            for doc in self.docs.values():
                wiki_sum = doc.get("summary") or ""
                wiki_is_llm = (doc.get("summary_source") == "llm")
                # 1) Wiki 요약 카드 매칭 점수 (가중치 보너스로 활용)
                sum_sc = 0.0
                s_toks = doc.get("summary_tokens") or []
                if s_toks and wiki_sum:
                    s_set = set(s_toks)
                    for qt, qcnt in q_freq.items():
                        if qt in s_set:
                            idf = math.log(1.0 + (n_docs - df.get(qt, 0) + 0.5) / (df.get(qt, 0) + 0.5))
                            sum_sc += idf * (1.2 if len(qt) >= 3 else 0.7) * min(2, qcnt)
                    if wiki_is_llm:
                        sum_sc *= 1.15

                # 2) 본문 청크 매칭 (원본 발췌 + 해당 문서의 Wiki 요약을 함께 결합)
                doc_hits: List[Tuple[float, Dict[str, Any]]] = []
                best_any: Optional[Tuple[float, Dict[str, Any]]] = None
                for ch in doc.get("chunks") or []:
                    c_toks = ch.get("tokens") or []
                    if not c_toks:
                        continue
                    c_cnt = Counter(c_toks)
                    sc = 0.0
                    hits = 0
                    for qt, qcnt in q_freq.items():
                        tf = c_cnt.get(qt, 0)
                        if tf > 0:
                            hits += 1
                            idf = math.log(1.0 + (n_docs - df.get(qt, 0) + 0.5) / (df.get(qt, 0) + 0.5))
                            tf_w = (tf * 2.2) / (tf + 1.2 * (0.35 + 0.65 * len(c_toks) / 60.0))
                            sc += idf * tf_w * min(2, qcnt)
                    sc *= _prose_quality_factor(ch["text"])
                    item = {
                        "doc": doc["name"],
                        "doc_id": doc["id"],
                        "loc": ch["loc"],
                        "snippet": ch["text"],
                        "wiki_summary": wiki_sum,
                        "wiki_is_llm": wiki_is_llm,
                        "score": round(max(sc, sum_sc), 2),
                        "is_wiki": False,
                    }
                    if best_any is None or sc > best_any[0]:
                        best_any = (sc, item)
                    if hits >= 2 or sc > 1.8:
                        doc_hits.append((sc + (0.25 * sum_sc if sum_sc > 1.2 else 0.0), item))

                if doc_hits:
                    candidates.extend(doc_hits)
                elif sum_sc > 1.2 and best_any is not None:
                    candidates.append((sum_sc, best_any[1]))

            candidates.sort(key=lambda x: x[0], reverse=True)
            picked: List[Dict[str, Any]] = []
            used_chars = 0
            seen_keys: set = set()
            doc_counts: Dict[str, int] = defaultdict(int)
            for _, item in candidates:
                k = (item["doc_id"], item["loc"], item["snippet"][:40])
                if k in seen_keys:
                    continue
                if per_doc_limit > 0 and doc_counts[item["doc_id"]] >= per_doc_limit:
                    continue
                if picked and used_chars + len(item["snippet"]) > max_chars:
                    continue
                seen_keys.add(k)
                doc_counts[item["doc_id"]] += 1
                picked.append(item)
                used_chars += len(item["snippet"])
                if len(picked) >= top_k:
                    break
            return picked


class TutorEngine:
    def __init__(self, proj: Project, cfg: Dict[str, Any], out_html: Optional[Path] = None):
        self.proj = proj
        self.cfg = dict(cfg)
        self.out_html = out_html
        if out_html is not None and (out_html.parent / "project_info.json").is_file():
            self.cache_dir = out_html.parent
        else:
            self.cache_dir = get_project_workspace_dir(proj.root)
        self.threads_path = self.cache_dir / "tutor_threads.json"
        self.llm_cache = LLMCache(self.cache_dir / "llm_tutor_cache.json")
        self.tr_cache = LLMCache(self.cache_dir / "wiki_tr_cache.json")
        self.wiki_q_cache = LLMCache(self.cache_dir / "wiki_q_cache.json")
        self.wiki = PaperWikiManager(self.proj.root, self.cache_dir)
        self.lock = threading.Lock()
        self.state = self._load_state()
        self.prewarm: Dict[str, Any] = {"active": False, "done": 0, "total": 0, "cached": 0, "stop": False}
        if self.cfg.get("use_llm") and self.cfg.get("base_url"):
            self.start_prewarm()

    def _load_state(self) -> Dict[str, Any]:
        try:
            if self.threads_path.is_file():
                d = json.loads(self.threads_path.read_text(encoding="utf-8"))
                if isinstance(d, dict):
                    return {
                        "threads": d.get("threads", {}) if isinstance(d.get("threads"), dict) else {},
                        "pins": d.get("pins", {}) if isinstance(d.get("pins"), dict) else {},
                        "done": d.get("done", []) if isinstance(d.get("done"), list) else [],
                        "bookmarks": d.get("bookmarks", []) if isinstance(d.get("bookmarks"), list) else [],
                        "last": d.get("last") if isinstance(d.get("last"), dict) else None,
                    }
        except Exception:
            pass
        return {"threads": {}, "pins": {}, "done": [], "bookmarks": [], "last": None}

    def _save_state(self) -> None:
        try:
            self.cache_dir.mkdir(parents=True, exist_ok=True)
            tmp = self.threads_path.with_suffix(".tmp")
            tmp.write_text(json.dumps(self.state, ensure_ascii=False, indent=2), encoding="utf-8")
            os.replace(tmp, self.threads_path)
        except OSError:
            pass

    def _client(self) -> LLMClient:
        extra = parse_extra_body(str(self.cfg.get("extra_body", "")))
        return LLMClient(
            str(self.cfg.get("base_url", "")),
            str(self.cfg.get("api_key", "")),
            str(self.cfg.get("model", "")),
            int(self.cfg.get("timeout", 90) or 90),
            extra,
        )

    def _llm_info(self) -> Dict[str, Any]:
        return {
            "use_llm": bool(self.cfg.get("use_llm")),
            "base_url": self.cfg.get("base_url", ""),
            "model": self.cfg.get("model", ""),
            "has_key": bool(self.cfg.get("api_key")),
            "extra_body": self.cfg.get("extra_body", ""),
        }

    def status_payload(self) -> Dict[str, Any]:
        with self.lock:
            return {
                "ok": True,
                "ver": VERSION,
                "code_hash": _self_code_hash(),
                "title": self.proj.root.name,
                "llm": self._llm_info(),
                "threads": self.state["threads"],
                "pins": self.state["pins"],
                "done": list(self.state.get("done", [])),
                "bookmarks": list(self.state.get("bookmarks", [])),
                "last": self.state.get("last"),
                "prewarm": dict(self.prewarm),
                "wiki": self.wiki.status(),
            }

    def _active_llm_client(self) -> Optional[LLMClient]:
        if not self.cfg.get("use_llm") or not self.cfg.get("base_url"):
            return None
        cl = self._client()
        if not cl.model:
            try:
                ids = cl.list_models()
                if ids:
                    cl.model = ids[0]
            except Exception:
                pass
        return cl if cl.model else None

    def _llm_expand_wiki_query(self, cl: LLMClient, ctx: Dict[str, Any], query: str = "") -> str:
        u, fr = ctx["u"], ctx["fr"]
        code_head = (ctx.get("code_slice") or "")[:1200]
        key = sha1(f"wq2|{cl.model}|{u.qual}|{ctx['l1']}|{ctx['l2']}|{query}|{code_head}")
        cached = self.wiki_q_cache.get(key)
        if isinstance(cached, str):
            return cached
        callees = ", ".join(c["name"] for c in (ctx.get("callees_info") or [])[:8])
        prompt = (
            f"Target: {u.disp} ({fr.rel})\n"
            + (f"Calls: {callees}\n" if callees else "")
            + (f"User question: {query}\n" if query else "")
            + f"Code:\n{code_head}\n\n"
            "Extract 6 to 10 precise English academic/engineering keywords or algorithm names that a research paper would use to describe the mathematical or physical method implemented in this code.\n"
            "Output ONLY comma-separated English terms (no bullets, no explanation). "
            "If the code is purely trivial utility, path/file setup, or glue code with no domain algorithm, output ONLY: NONE"
        )
        try:
            raw, _ = cl.complete_messages(
                [{"role": "system", "content": "You generate concise English academic search keywords for code-to-paper retrieval."},
                 {"role": "user", "content": prompt}],
                max_tokens=120, temperature=0.0,
            )
            txt = clean_llm_text(raw, keep_md=False).strip()
            if txt.upper() in ("NONE", "N/A", "없음"):
                res = "__NONE__"
            else:
                res = re.sub(r"\s+", " ", txt)[:260]
            self.wiki_q_cache.put(key, res)
            return res
        except Exception:
            return ""

    def _llm_rerank_wiki_refs(self, cl: LLMClient, ctx: Dict[str, Any], query: str,
                              candidates: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        if not candidates:
            return []
        u, fr = ctx["u"], ctx["fr"]
        sig = "|".join(f"{c['doc_id']}:{c['loc']}:{c['snippet'][:24]}" for c in candidates)
        key = sha1(f"wr3|{cl.model}|{self.wiki.wiki_hash}|{u.qual}|{ctx['l1']}|{ctx['l2']}|{query}|{sig}")
        cached = self.wiki_q_cache.get(key)
        if isinstance(cached, list):
            out_c: List[Dict[str, Any]] = []
            for entry in cached:
                if isinstance(entry, dict) and isinstance(entry.get("i"), int) and 0 <= entry["i"] < len(candidates):
                    it = dict(candidates[entry["i"]])
                    if entry.get("link"):
                        it["code_link"] = str(entry["link"])
                    out_c.append(it)
            return out_c
        code_head = (ctx.get("code_slice") or "")[:900]
        cand_lines = [
            f"[{i + 1}] ({c['doc']} · {c['loc']}): {short(c['snippet'].replace(chr(10), ' '), 280)}"
            for i, c in enumerate(candidates)
        ]
        prompt = (
            f"Target code: {u.disp} ({fr.rel})\n"
            + (f"User question: {query}\n" if query else "")
            + f"Code:\n{code_head}\n\n"
            "Candidate paper excerpts:\n" + "\n".join(cand_lines) + "\n\n"
            "Select ONLY the candidates (at most 4, most relevant first) that directly explain the algorithm, equations, coordinate frame, physical model, or mathematical concept implemented in this code.\n"
            "Reject unrelated instrument/mission descriptions, generic introductions, or unrelated metrics.\n"
            "For each selected candidate, write ONE line in Korean explaining how this code connects to that excerpt (1~2 concise sentences, use backticks for code symbols and avoid LaTeX $):\n"
            "<number>: <Korean connection explanation>\n"
            "If none are directly relevant, output ONLY: NONE"
        )
        try:
            raw, _ = cl.complete_messages(
                [{"role": "system", "content": "You are a strict relevance judge and concise Korean technical explainer for code-to-paper retrieval."},
                 {"role": "user", "content": prompt}],
                max_tokens=420, temperature=0.1,
            )
            txt = clean_llm_text(raw, keep_md=True).strip()
            picked: List[Dict[str, Any]] = []
            seen_i: set = set()
            if txt.upper() != "NONE":
                for ln in txt.splitlines():
                    m = re.match(r"^\s*(?:[-*•]\s*)?\[?(\d+)\]?\s*[:：\-]\s*(.+)$", ln)
                    if m:
                        idx = int(m.group(1)) - 1
                        note = m.group(2).strip()
                        if 0 <= idx < len(candidates) and idx not in seen_i and note:
                            seen_i.add(idx)
                            picked.append({"i": idx, "link": note})
                            if len(picked) >= 4:
                                break
                if not picked and "NONE" not in txt.upper():
                    for m in re.findall(r"\d+", txt):
                        idx = int(m) - 1
                        if 0 <= idx < len(candidates) and idx not in seen_i:
                            seen_i.add(idx)
                            picked.append({"i": idx, "link": ""})
                            if len(picked) >= 4:
                                break
            self.wiki_q_cache.put(key, picked)
            res_list: List[Dict[str, Any]] = []
            for entry in picked:
                it = dict(candidates[entry["i"]])
                if entry.get("link"):
                    it["code_link"] = str(entry["link"])
                res_list.append(it)
            return res_list
        except Exception:
            return candidates[:4]

    def _wiki_refs(self, ctx: Dict[str, Any], query: str = "") -> List[Dict[str, Any]]:
        if not self.wiki or self.wiki.total_chunks == 0:
            return []
        u, fr = ctx["u"], ctx["fr"]
        parts = [u.disp, fr.rel, u.static.get("one", ""), query]
        extra = list(ctx.get("reads") or [])[:10] + list(ctx.get("writes") or [])[:8]
        extra += [c["name"] for c in (ctx.get("callees_info") or [])[:5]]
        if ctx.get("var_name"):
            extra.append(str(ctx["var_name"]))

        cl = self._active_llm_client()
        if cl is not None:
            exp = self._llm_expand_wiki_query(cl, ctx, query)
            if exp == "__NONE__" and not query:
                return []
            q_str = (exp + " " + " ".join(p for p in parts if p)).strip() if exp else " ".join(p for p in parts if p)
            cands = self.wiki.search(q_str, extra_tokens=extra, top_k=12, max_chars=14000, per_doc_limit=3)
            if not cands:
                return []
            return self._llm_rerank_wiki_refs(cl, ctx, query, cands)

        return self.wiki.search(" ".join(p for p in parts if p), extra_tokens=extra, top_k=6, max_chars=6000, per_doc_limit=2)

    def _format_wiki_prompt(self, refs: List[Dict[str, Any]]) -> str:
        if not refs:
            return ""
        lines = ["\n[관련 논문 / Wiki 참고 근거]"]
        used = 0
        for r in refs[:4]:
            sn = r["snippet"]
            if used > 0 and used + len(sn) > 1700:
                continue
            lines.append(f"- ({r['doc']} · {r['loc']}): {sn}")
            used += len(sn)
        lines.append("위 참고 근거가 코드의 수식·변수 의미·좌표계·가정과 관련이 있다면 출처(파일명·위치)와 함께 설명에 반영하라. 논문에 없는 내용은 지어내지 마라.")
        return "\n".join(lines)

    def translate_wiki_snippet(self, text: str) -> Dict[str, Any]:
        src = (text or "").strip()
        if not src:
            return {"ok": False, "error": "번역할 본문이 비어 있습니다."}
        if not self.cfg.get("use_llm") or not self.cfg.get("base_url"):
            return {"ok": False, "error": "LLM이 연결되어 있지 않아 번역할 수 없습니다."}
        cl = self._client()
        if not cl.model:
            try:
                ids = cl.list_models()
                if ids:
                    cl.model = ids[0]
            except Exception:
                pass
        if not cl.model:
            return {"ok": False, "error": "LLM 모델명이 설정되지 않았습니다."}
        key = sha1(f"tr|{cl.model}|{src}")
        cached = self.tr_cache.get(key)
        if isinstance(cached, str) and cached:
            return {"ok": True, "ko": cached, "cached": True}
        try:
            raw, _ = cl.complete_messages(
                [
                    {"role": "system", "content": "너는 공학·알고리즘 논문 전문 번역가다. 주어진 발췌문을 자연스럽고 정확한 한국어로 번역하라. 변수명·기호·고유 전문용어는 백틱(`x_k`)이나 괄호로 원문을 병기하고, LaTeX $ 기호 대신 유니코드/일반 텍스트를 사용하며 원문에 없는 내용을 지어내지 마라."},
                    {"role": "user", "content": src},
                ],
                max_tokens=1200, temperature=0.1,
            )
            ko = clean_llm_text(raw, keep_md=True)
            if ko:
                self.tr_cache.put(key, ko)
                return {"ok": True, "ko": ko, "cached": False}
            return {"ok": False, "error": "번역 결과가 비어 있습니다."}
        except Exception as e:
            return {"ok": False, "error": f"번역 실패: {e}"}

    def open_wiki_doc(self, doc_id: str) -> Dict[str, Any]:
        doc = self.wiki.get_doc(doc_id)
        if not doc:
            return {"ok": False, "error": "등록된 문서를 찾을 수 없습니다."}
        fp = Path(doc["path"])
        if not fp.is_file():
            return {"ok": False, "error": f"원본 파일이 존재하지 않습니다: {fp}"}
        try:
            if os.name == "nt":
                os.startfile(str(fp))  # type: ignore[attr-defined]
            elif sys.platform == "darwin":
                subprocess.Popen(["open", str(fp)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            else:
                subprocess.Popen(["xdg-open", str(fp)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            return {"ok": True, "path": str(fp)}
        except Exception as e:
            return {"ok": False, "error": f"파일 열기 실패: {e}"}

    def update_config(self, body: Dict[str, Any]) -> Dict[str, Any]:
        with self.lock:
            for k in ("base_url", "model", "extra_body"):
                if k in body:
                    self.cfg[k] = str(body[k] or "").strip()
            if "api_key" in body and body["api_key"] != "__KEEP__":
                self.cfg["api_key"] = str(body["api_key"] or "").strip()
            if "use_llm" in body:
                self.cfg["use_llm"] = bool(body["use_llm"])
            save_config(self.cfg)
        if not self.cfg.get("use_llm"):
            self.prewarm["stop"] = True
            return {"ok": True, "connected": False, "message": "정적 맥락 튜터 모드로 저장되었습니다.",
                    "llm": self._llm_info(), "prewarm": dict(self.prewarm)}
        if not self.cfg.get("base_url"):
            return {"ok": True, "connected": False, "message": "Base URL이 비어 있습니다.",
                    "llm": self._llm_info(), "prewarm": dict(self.prewarm)}
        cl = self._client()
        logs: List[str] = []
        ok = cl.preflight(logs.append)
        if ok and cl.model and not self.cfg.get("model"):
            with self.lock:
                self.cfg["model"] = cl.model
                save_config(self.cfg)
        if ok:
            self.start_prewarm()
        msg = " · ".join(logs) if logs else ("연결 성공" if ok else "연결 실패")
        return {"ok": True, "connected": ok, "message": msg, "llm": self._llm_info(), "prewarm": dict(self.prewarm)}

    def start_prewarm(self, max_items: int = 0) -> Dict[str, Any]:
        if not self.cfg.get("use_llm") or not self.cfg.get("base_url"):
            return {"ok": False, "message": "LLM이 활성화되지 않았습니다.", "prewarm": dict(self.prewarm)}
        with self.lock:
            if self.prewarm.get("active"):
                return {"ok": True, "prewarm": dict(self.prewarm)}
            limit = max_items or int(self.cfg.get("max_calls", 150) or 150)
            order_ids = list(self.proj.order.get("down", []))
            seen = set(order_ids)
            for u in self.proj.units:
                if u.kind == "function" and u.id not in seen:
                    order_ids.append(u.id)
            targets = [self.proj.units[i] for i in order_ids
                       if 0 <= i < len(self.proj.units) and self.proj.units[i].kind == "function"][:limit]
            self.prewarm = {"active": True, "done": 0, "total": len(targets), "cached": 0, "stop": False}

        def run_prewarm() -> None:
            fails = 0
            try:
                for u in targets:
                    if self.prewarm.get("stop") or not self.cfg.get("use_llm"):
                        break
                    res = self.brief(u.id, u.file, u.line, u.end, "beginner", force=False)
                    with self.lock:
                        self.prewarm["done"] += 1
                        if res.get("source") == "llm":
                            self.prewarm["cached"] += 1
                            fails = 0
                        else:
                            fails += 1
                    if fails >= 4:
                        break
            finally:
                with self.lock:
                    self.prewarm["active"] = False

        threading.Thread(target=run_prewarm, daemon=True).start()
        return {"ok": True, "prewarm": dict(self.prewarm)}

    def update_study_state(self, body: Dict[str, Any]) -> Dict[str, Any]:
        with self.lock:
            if "done" in body and isinstance(body["done"], list):
                self.state["done"] = sorted({int(x) for x in body["done"] if isinstance(x, (int, float))})
            if "bookmarks" in body and isinstance(body["bookmarks"], list):
                self.state["bookmarks"] = sorted({int(x) for x in body["bookmarks"] if isinstance(x, (int, float))})
            if "last" in body and isinstance(body["last"], dict):
                last = dict(body["last"])
                last["ts"] = time.strftime("%m/%d %H:%M")
                self.state["last"] = last
            self._save_state()
            return {
                "ok": True,
                "done": list(self.state["done"]),
                "bookmarks": list(self.state["bookmarks"]),
                "last": self.state["last"],
            }

    def _unit_and_range(self, uid: int, file_id: int, l1: int, l2: int) -> Tuple[Unit, FileRec, int, int]:
        if 0 <= uid < len(self.proj.units):
            u = self.proj.units[uid]
        elif 0 <= file_id < len(self.proj.files) and self.proj.files[file_id].module_unit:
            u = self.proj.files[file_id].module_unit  # type: ignore[assignment]
        else:
            u = self.proj.units[0]
        fr = self.proj.files[u.file]
        if l1 <= 0 or l2 <= 0:
            l1, l2 = u.line, u.end
        l1 = max(1, min(l1, len(fr.lines)))
        l2 = max(l1, min(l2, len(fr.lines)))
        return u, fr, l1, l2

    def build_block_context(self, uid: int, file_id: int, l1: int, l2: int) -> Dict[str, Any]:
        u, fr, l1, l2 = self._unit_and_range(uid, file_id, l1, l2)
        is_whole = (l1 <= u.line and l2 >= u.end)
        exact_step = next((s for s in u.steps if s["l1"] == l1 and s["l2"] == l2), None)
        overlap_steps = [s for s in u.steps if not (s["l2"] < l1 or s["l1"] > l2)]

        reads: List[str] = []
        writes: List[str] = []
        muts: List[str] = []
        calls: List[list] = []
        seen_call: set = set()
        stmt_summaries: List[str] = []
        for ln in range(l1, l2 + 1):
            inf = fr.info.get(ln)
            if not inf or inf.get("k") in ("cont", "blank", "comment"):
                continue
            for r in inf.get("r") or []:
                if r not in reads:
                    reads.append(r)
            for w in inf.get("w") or []:
                if w not in writes:
                    writes.append(w)
            for m in inf.get("m") or []:
                if m not in muts:
                    muts.append(m)
            for c in inf.get("c") or []:
                if c and c[0] not in seen_call:
                    seen_call.add(c[0])
                    calls.append(c)
            if inf.get("x") and len(stmt_summaries) < 12:
                stmt_summaries.append(f"L{ln}: {inf['x']}")

        param_names = {p["name"] for p in u.params if p["name"] != u.self_name}
        from_earlier: List[dict] = []
        for r in reads:
            if r == u.self_name:
                continue
            v = u.vars.get(r)
            if not v:
                continue
            prior = [d for d in v.get("defs", []) if d[0] < l1]
            if r in param_names or prior:
                from_earlier.append({
                    "name": r, "type": v.get("type", ""),
                    "from": f"매개변수(L{u.line})" if r in param_names and not prior else f"L{prior[-1][0]} (`{prior[-1][1]}`)",
                })

        used_later: List[dict] = []
        for w in writes + [m for m in muts if m not in writes]:
            v = u.vars.get(w)
            later = [us for us in (v.get("uses", []) if v else []) if us > l2]
            used_later.append({
                "name": w, "type": v.get("type", "") if v else "",
                "later": later[:5], "is_attr": w.startswith("self."),
            })

        callees_info: List[dict] = []
        ext_info: List[dict] = []
        for c in calls:
            lab, cid, q, mean = c[0], c[1], c[2], c[3]
            if cid >= 0 and cid < len(self.proj.units):
                cu = self.proj.units[cid]
                callees_info.append({
                    "id": cid, "name": cu.disp, "sig": unit_signature(cu),
                    "one": (cu.ai or {}).get("s") or cu.static.get("one", ""),
                    "loc": f"{self.proj.files[cu.file].rel}:{cu.line}",
                })
            else:
                ext_info.append({"name": lab, "meaning": mean})

        callers_info: List[dict] = []
        for cid, e in list(u.callers.items())[:5]:
            cu = self.proj.units[cid]
            callers_info.append({
                "id": cid, "name": cu.disp,
                "loc": f"{self.proj.files[cu.file].rel}", "lines": e.get("lines", [])[:4],
            })

        code_slice = "\n".join(f"{ln}: {fr.lines[ln - 1]}" for ln in range(l1, min(l2, l1 + 79) + 1))
        if l2 - l1 + 1 > 80:
            code_slice += f"\n... ({l2 - l1 + 1 - 80}줄 생략)"
        full_code = ""
        if not is_whole and (u.end - u.line + 1) <= 90:
            full_code = "\n".join(f"{ln}: {fr.lines[ln - 1]}" for ln in range(u.line, u.end + 1))

        return {
            "u": u, "fr": fr, "l1": l1, "l2": l2, "is_whole": is_whole,
            "exact_step": exact_step, "overlap_steps": overlap_steps,
            "reads": reads, "writes": writes, "muts": muts, "calls": calls,
            "from_earlier": from_earlier, "used_later": used_later,
            "callees_info": callees_info, "ext_info": ext_info, "callers_info": callers_info,
            "stmt_summaries": stmt_summaries, "code_slice": code_slice, "full_code": full_code,
        }

    def _suggestions(self, ctx: Dict[str, Any]) -> List[dict]:
        u, fr, l1, l2 = ctx["u"], ctx["fr"], ctx["l1"], ctx["l2"]
        lang_nm = LANG_LABELS.get(fr.lang, fr.lang.upper())
        lang_ico = {"py": "🐍", "js": "🟨", "ts": "🟦", "tsx": "🟦", "c": "⚙️", "cpp": "⚙️", "matlab": "📐"}.get(fr.lang, "🧩")
        sample_v = ctx["from_earlier"][0]["name"] if ctx["from_earlier"] else (u.params[0]["name"] if u.params else "")
        callee_n = ctx["callees_info"][0]["name"] if ctx["callees_info"] else ""
        s_trace = f"예시 값을 넣어서 `{sample_v}` 등이 어떻게 변하는지 따라가 보기" if sample_v else "실제 예시 값을 대입해서 실행 순서 따라가 보기"
        s_conn = f"`{callee_n}` 등 호출 함수와 앞뒤 흐름 연결해 보기" if callee_n else "이 구간 앞뒤(호출자·다음 단계)와 데이터 연결 보기"
        return [
            {"mode": "trace", "label": "💡 예시 값 대입해서 추적하기", "q": s_trace},
            {"mode": "why", "label": "🧩 이 구간의 존재 이유(Why)와 맥락", "q": f"L{l1}~L{l2} 구간은 왜 필요하고 전체에서 무슨 역할을 해?"},
            {"mode": "connect", "label": "🔗 호출 함수·데이터 연결 흐름", "q": s_conn},
            {"mode": "syntax", "label": f"{lang_ico} 사용된 {lang_nm} 문법 쉽게 풀이", "q": f"L{l1}~L{l2} 에 쓰인 {lang_nm} 문법·표현을 초보자 눈높이로 풀어줘"},
        ]

    def _static_brief(self, ctx: Dict[str, Any], level: str = "beginner") -> Dict[str, Any]:
        u, l1, l2 = ctx["u"], ctx["l1"], ctx["l2"]
        step = ctx["exact_step"]
        steps = ctx["overlap_steps"]
        is_whole = ctx["is_whole"]

        if step:
            title = f"{u.disp} — Step {step['id']}: {step['t']}"
            intent = f"{step['d']} {step['w']}".strip()
        elif is_whole:
            title = f"{u.disp} — 전체 맥락 요약 ({u.end - u.line + 1}줄)"
            ai_one = (u.ai or {}).get("s")
            base_one = ai_one or u.static.get("one", "")
            if u.steps:
                intent = f"{base_one} 이 코드는 크게 **{len(u.steps)}개의 논리 단계**로 나뉘어 순서대로 역할을 수행합니다."
            else:
                intent = base_one or f"`{u.disp}` 전체를 실행합니다."
        else:
            title = f"{u.disp} — 선택 구간 L{l1}–L{l2} ({l2 - l1 + 1}줄)"
            if steps:
                names = ", ".join(f"Step {s['id']}({s['t']})" for s in steps[:3])
                intent = f"선택한 {l2 - l1 + 1}줄은 **{names}** 흐름을 담당합니다. " + " ".join(s["d"] for s in steps[:2])
            else:
                intent = f"L{l1}~L{l2} 구간을 하나의 묶음으로 실행하여 상태를 갱신하거나 값을 계산합니다."

        flow: List[str] = []
        if is_whole and u.steps:
            for s in u.steps:
                flow.append(f"**Step {s['id']} · {s['t']}** (`L{s['l1']}–L{s['l2']}`): {s['d']}")
        elif steps and not step:
            for s in steps:
                flow.append(f"**Step {s['id']} · {s['t']}** (`L{s['l1']}–L{s['l2']}`): {s['d']}")
        else:
            if ctx["from_earlier"]:
                ins = ", ".join(f"`{x['name']}`" for x in ctx["from_earlier"][:4])
                flow.append(f"**입력 받기**: {ins} 값을 앞선 단계(또는 매개변수)에서 넘겨받습니다.")
            if ctx["callees_info"] or ctx["ext_info"]:
                cs = [f"`{c['name']}()`" for c in ctx["callees_info"][:3]] + [f"`{e['name']}`" for e in ctx["ext_info"][:2]]
                flow.append(f"**핵심 처리·위임**: {', '.join(cs)} 을(를) 호출해 작업을 처리합니다.")
            elif ctx["stmt_summaries"]:
                flow.append(f"**핵심 처리**: {ctx['stmt_summaries'][0]}")
            if ctx["used_later"] or (u.rets and is_whole):
                outs = ", ".join(f"`{x['name']}`" for x in ctx["used_later"][:4])
                if outs:
                    flow.append(f"**결과 전달**: 계산한 {outs} 을(를) 다음 단계로 넘깁니다.")
                elif u.rets:
                    flow.append(f"**반환**: `{u.rets[0]}` 형태를 호출자에게 돌려줍니다.")
            if not flow:
                flow = ctx["stmt_summaries"][:4] or [f"L{l1}–L{l2} 구문을 순차 실행합니다."]

        df_parts: List[str] = []
        if ctx["from_earlier"]:
            df_parts.append("들어오는 값: " + ", ".join(f"`{x['name']}`({x['from']})" for x in ctx["from_earlier"][:4]))
        if ctx["used_later"]:
            df_parts.append("내보내는 값: " + ", ".join(
                f"`{x['name']}`" + ("(객체 상태)" if x["is_attr"] else f"(→ L{x['later'][0]} 등에서 사용)" if x["later"] else "")
                for x in ctx["used_later"][:4]
            ))
        if ctx["callees_info"]:
            df_parts.append("연결 함수: " + ", ".join(f"`{c['name']}` ({short(c['one'], 45)})" for c in ctx["callees_info"][:3]))
        data_flow = "\n".join(f"- {p}" for p in df_parts) if df_parts else "이 구간 내부에서 지역 상태를 계산하거나 직접 흐름을 제어합니다."

        cauts: List[str] = []
        if u.is_recursive:
            cauts.append("자기 자신을 다시 호출하는 재귀 구조이므로 종료 조건(기저 조건)을 먼저 확인하세요.")
        if ctx["muts"]:
            cauts.append(f"`{', '.join(ctx['muts'][:3])}` 컨테이너의 내용이 제자리(in-place)에서 수정됩니다.")
        if u.effects:
            cauts.append("외부 부작용 포함: " + ", ".join(EFFECT_LABELS[e] for e in sorted(u.effects)))
        if (u.ai or {}).get("c") and is_whole:
            cauts.append(u.ai["c"])  # type: ignore[index]
        caution = ("\n".join(cauts) if len(cauts) == 1 else "\n".join(f"- {c}" for c in cauts)) if cauts else "특별한 외부 부작용 없이 비교적 순수한 논리 흐름입니다."

        if level == "concise":
            flow = flow[:3]

        return {
            "ok": True,
            "unit_id": u.id,
            "range": [l1, l2],
            "step_id": step["id"] if step else 0,
            "title": title,
            "source": "static",
            "model": "",
            "intent": intent,
            "flow": flow,
            "data_flow": data_flow,
            "caution": caution,
            "suggestions": self._suggestions(ctx),
            "llm_note": "",
        }

    def _ctx_prompt_block(self, ctx: Dict[str, Any]) -> str:
        u, fr, l1, l2 = ctx["u"], ctx["fr"], ctx["l1"], ctx["l2"]
        lang_nm = LANG_LABELS.get(fr.lang, fr.lang.upper())
        lines = [
            f"[대상] {u.disp} ({fr.rel}:{u.line}-{u.end}) · 언어: {lang_nm} / 선택 구간 L{l1}-L{l2}",
            f"[시그니처] {unit_signature(u)}",
        ]
        if u.static.get("one"):
            lines.append(f"[정적 요약] {u.static['one']}")
        if ctx["callers_info"]:
            lines.append("[이 함수를 호출하는 곳] " + ", ".join(f"{c['name']}({c['loc']})" for c in ctx["callers_info"]))
        if ctx["from_earlier"]:
            lines.append("[구간에 들어오는 변수] " + ", ".join(
                f"{x['name']}:{x['type'] or '?'} ({x['from']})" for x in ctx["from_earlier"]))
        if ctx["callees_info"]:
            lines.append("[구간에서 호출하는 프로젝트 함수]")
            for c in ctx["callees_info"][:5]:
                lines.append(f"  - {c['sig']} ({c['loc']}): {short(c['one'], 80)}")
        if ctx["full_code"]:
            lines.append("[함수 전체 코드]\n" + ctx["full_code"])
        lines.append(f"[선택 구간 코드 L{l1}-L{l2}]\n" + ctx["code_slice"])
        return "\n".join(lines)

    def brief(self, uid: int, file_id: int, l1: int, l2: int, level: str = "beginner",
              force: bool = False) -> Dict[str, Any]:
        ctx = self.build_block_context(uid, file_id, l1, l2)
        refs = self._wiki_refs(ctx)
        base = self._static_brief(ctx, level=level)
        if refs:
            base["refs"] = refs
        if not self.cfg.get("use_llm") or not self.cfg.get("base_url"):
            return base
        cl = self._client()
        if not cl.model:
            try:
                ids = cl.list_models()
                if ids:
                    cl.model = ids[0]
                    with self.lock:
                        self.cfg["model"] = cl.model
                        save_config(self.cfg)
            except Exception:
                pass
        if not cl.model:
            base["llm_note"] = "LLM 모델명이 설정되지 않아 정적 맥락 해설로 표시합니다."
            return base

        key = sha1(f"brief|{PROMPT_VERSION}|{cl.model}|{level}|{self.wiki.wiki_hash}|{ctx['u'].qual}|{ctx['l1']}|{ctx['l2']}|{ctx['code_slice']}")
        if not force:
            cached = self.llm_cache.get(key)
            if isinstance(cached, dict):
                out_c = dict(cached)
                if refs:
                    out_c["refs"] = refs
                return out_c

        tone = "초보자가 비유와 맥락으로 쉽게 이해할 수 있게" if level == "beginner" else "핵심 요점만 간결하게"
        user_p = (
            self._ctx_prompt_block(ctx)
            + self._format_wiki_prompt(refs)
            + f"\n\n[요청] 위 선택 구간(L{ctx['l1']}-L{ctx['l2']})을 줄 단위로 직역하지 말고, "
            f"하나의 의미 덩어리로 묶어서 {tone} 설명해 달라.\n"
            "[출력 형식 — 각 태그로 시작]\n"
            "의도: (이 구간이 왜 존재하고 전체에서 어떤 역할을 하는지 1~2문장)\n"
            "흐름1: (논리 단계 1)\n"
            "흐름2: (논리 단계 2)\n"
            "흐름3: (논리 단계 3, 필요 없으면 생략)\n"
            "데이터: (들어오는 값 → 변환/호출 → 나가는 값 한 문장)\n"
            "주의: (초보자가 헷갈릴 점 한 문장, 없으면 없음)\n"
            "추천질문1: (이 코드를 본 초보자가 이어서 물어볼 만한 구체적 질문 1개)\n"
            "추천질문2: (꼬리 질문 1개)"
        )
        try:
            raw, _ = cl.complete_messages(
                [{"role": "system", "content": TUTOR_SYS_PROMPT}, {"role": "user", "content": user_p}],
                max_tokens=1400, temperature=0.2,
            )
            txt = clean_llm_text(raw, keep_md=True)
            parsed: Dict[str, str] = {}
            flows: List[str] = []
            extra_sugg: List[dict] = []
            cur_k = ""
            for ln in txt.splitlines():
                m = re.match(r"^\s*(?:[-*•]\s*)?(의도|흐름\d*|데이터|주의|추천질문\d*)\s*[:：]\s*(.+)$", ln)
                if m:
                    cur_k = m.group(1)
                    val = m.group(2).strip()
                    if cur_k.startswith("흐름"):
                        flows.append(val)
                    elif cur_k.startswith("추천질문"):
                        extra_sugg.append({"mode": "chat", "label": "✨ " + short(val, 42), "q": val})
                    else:
                        parsed[cur_k] = val
                elif ln.strip() and cur_k:
                    if cur_k.startswith("흐름") and flows:
                        flows[-1] += "\n" + ln.strip()
                    elif cur_k in parsed:
                        parsed[cur_k] += "\n" + ln.strip()
            res = dict(base)
            res["source"] = "llm"
            res["model"] = cl.model
            if parsed.get("의도"):
                res["intent"] = parsed["의도"]
            elif not flows and txt:
                res["intent"] = txt
            if flows:
                res["flow"] = flows
            if parsed.get("데이터"):
                res["data_flow"] = parsed["데이터"]
            if parsed.get("주의") and parsed["주의"] not in ("없음", "없음.", "-"):
                res["caution"] = parsed["주의"]
            if extra_sugg:
                res["suggestions"] = extra_sugg[:2] + base["suggestions"][:3]
            self.llm_cache.put(key, res)
            return res
        except Exception as e:
            base["llm_note"] = f"LLM 응답 실패로 정적 맥락 해설로 표시합니다 ({e})"
            return base

    def _sample_value(self, name: str, typ: str, default: Optional[str]) -> str:
        if default and default != "None":
            return default
        t = (typ or "").lower()
        nl = name.lower()
        if "bool" in t or nl.startswith(("is_", "has_", "use_", "open_")):
            return "True"
        if "int" in t or nl in ("i", "j", "k", "n", "idx", "line", "l1", "l2", "depth", "port"):
            return "1" if "l" in nl else "0"
        if "float" in t:
            return "1.5"
        if "list" in t or nl.endswith("s") or nl in ("items", "lines", "rest", "parts", "nodes", "edges"):
            return '["a", "b"]' if "rest" in nl or "parts" in nl or "lines" in nl else "[1, 2]"
        if "dict" in t or nl in ("cfg", "vt", "info", "data", "body", "ctx"):
            return '{"key": "val"}'
        if "set" in t:
            return '{"x"}'
        if "path" in t or "dir" in nl or "file" in nl:
            return 'Path("project/app.py")'
        if "str" in t or nl in ("name", "base", "text", "msg", "q", "kind"):
            return f'"{name}_ex"'
        return f"<{typ or '값'}>"

    def _static_answer(self, ctx: Dict[str, Any], question: str, mode: str, level: str) -> Tuple[str, List[dict]]:
        u, fr, l1, l2 = ctx["u"], ctx["fr"], ctx["l1"], ctx["l2"]
        suggs = self._suggestions(ctx)

        if mode == "trace":
            samples = []
            for p in u.params:
                if p["name"] == u.self_name:
                    continue
                samples.append(f"- `{p['name']}` = `{self._sample_value(p['name'], p['ann'], p['default'])}`")
            for x in ctx["from_earlier"][:4]:
                if not any(f"`{x['name']}`" in s for s in samples):
                    samples.append(f"- `{x['name']}` = `{self._sample_value(x['name'], x['type'], None)}` *({x['from']})*")
            if not samples:
                samples.append("- 외부 입력 변수 없이 내부 상수/리터럴로 시작합니다.")

            steps_trace: List[str] = []
            for ln in range(l1, min(l2, l1 + 25) + 1):
                inf = fr.info.get(ln)
                if not inf or inf.get("k") in ("cont", "blank", "comment", "docstring"):
                    continue
                k = inf.get("k")
                code_ln = short(fr.lines[ln - 1].strip(), 64)
                if k in ("if", "elif"):
                    steps_trace.append(f"- **L{ln} 조건 확인** (`{code_ln}`): {inf.get('h') or inf.get('x', '')}")
                elif k in ("for", "while"):
                    steps_trace.append(f"- **L{ln} 반복 진입** (`{code_ln}`): 원소가 있는 동안 1회씩 아래 블록을 돌며 상태를 누적합니다.")
                elif k in ("assign", "augassign", "annassign"):
                    ws = ", ".join(f"`{w}`" for w in (inf.get("w") or [])) or "변수"
                    steps_trace.append(f"- **L{ln} 값 갱신** (`{code_ln}`): 계산 결과를 {ws} 에 담습니다.")
                elif k == "callstmt":
                    steps_trace.append(f"- **L{ln} 동작 실행** (`{code_ln}`): {inf.get('x', '')}")
                elif k == "return":
                    steps_trace.append(f"- **L{ln} 결과 반환** (`{code_ln}`): 이 시점의 값을 돌려주며 함수를 끝냅니다.")
                if len(steps_trace) >= 8:
                    break
            if not steps_trace:
                steps_trace.append(f"- `L{l1}–L{l2}` 문장들을 위에서 아래로 실행합니다.")

            outs = [f"`{x['name']}`" for x in ctx["used_later"][:5]]
            tail = f"이 구간이 끝나면 {', '.join(outs)} 값이 준비되어 다음 단계로 넘어갑니다." if outs else "구간 내 작업을 완료하고 흐름을 이어갑니다."
            ans = (
                f"**1️⃣ 가정한 입력값 예시**\n" + "\n".join(samples)
                + f"\n\n**2️⃣ L{l1}–L{l2} 단계별 실행 흐름**\n" + "\n".join(steps_trace)
                + f"\n\n**3️⃣ 구간 종료 후 상태**\n- {tail}"
            )
            return ans, [s for s in suggs if s["mode"] != "trace"]

        if mode == "why":
            callers_txt = (
                ", ".join(f"`{c['name']}`({c['loc']})" for c in ctx["callers_info"][:3])
                if ctx["callers_info"] else "외부/진입점에서 직접 실행되거나 콜백으로 호출"
            )
            step = ctx["exact_step"]
            purpose = step["w"] if step else (ctx["overlap_steps"][0]["w"] if ctx["overlap_steps"] else "함수의 중간 결과를 계산해 다음 로직으로 넘기기 위함입니다.")
            in_txt = ", ".join(f"`{x['name']}`" for x in ctx["from_earlier"][:4]) or "새로 입력받는 지역 값"
            out_txt = ", ".join(f"`{x['name']}`" for x in ctx["used_later"][:4]) or (f"반환값 `{u.rets[0]}`" if u.rets else "상태 변경/부작용")
            ans = (
                f"**🧩 L{l1}–L{l2} 구간이 존재하는 이유**\n"
                f"- **전체 함수의 목적**: {u.static.get('one', u.disp)}\n"
                f"- **누가 이 함수를 부르나**: {callers_txt}\n"
                f"- **이 구간의 핵심 역할**: {purpose}\n"
                f"- **전후 연결**: 앞선 {in_txt} 을(를) 받아 처리한 뒤, 뒤쪽에서 쓸 {out_txt} 으로 연결해 줍니다."
            )
            return ans, [s for s in suggs if s["mode"] != "why"]

        if mode == "connect":
            c_in = "\n".join(f"- `{c['name']}` ({c['loc']} L{','.join(map(str, c['lines']))})" for c in ctx["callers_info"]) or "- 직접 호출하는 프로젝트 함수 없음 (진입점 또는 콜백 후보)"
            c_out = "\n".join(f"- **`{c['name']}`** (`{c['loc']}`)\n  시그니처: `{c['sig']}`\n  역할: {c['one']}" for c in ctx["callees_info"])
            e_out = "\n".join(f"- `{e['name']}`: {e['meaning'] or '외부/라이브러리 호출'}" for e in ctx["ext_info"])
            sub_out = (c_out + ("\n" + e_out if e_out else "")).strip() or "- 이 구간 안에서는 다른 함수를 호출하지 않고 자체 계산만 수행합니다."
            ans = (
                f"**🔗 L{l1}–L{l2} 호출·데이터 연결 지도**\n\n"
                f"**▲ 이 함수를 부르는 상위 호출자**\n{c_in}\n\n"
                f"**▼ 이 구간 안에서 부르는 하위 함수/도구**\n{sub_out}"
            )
            return ans, [s for s in suggs if s["mode"] != "connect"]

        if mode == "syntax":
            found: List[Tuple[str, str]] = []
            seen_syn: set = set()
            lang_nm = LANG_LABELS.get(fr.lang, fr.lang.upper())
            lang_ico = {"py": "🐍", "js": "🟨", "ts": "🟦", "tsx": "🟦", "c": "⚙️", "cpp": "⚙️", "matlab": "📐"}.get(fr.lang, "🧩")

            def add_syn(tag: str, exp: str) -> None:
                if tag not in seen_syn and exp:
                    seen_syn.add(tag)
                    found.append((tag, exp))

            if fr.lang == "py" and isinstance(u.node, ast.AST):
                for node in ast.walk(u.node):
                    ln = getattr(node, "lineno", 0)
                    if not (l1 <= ln <= l2):
                        continue
                    if isinstance(node, (ast.ListComp, ast.SetComp, ast.DictComp, ast.GeneratorExp)):
                        add_syn("컴프리헨션 (`[x for x in ...]`)", "반복문과 리스트 추가(`append`)를 한 줄로 줄여 새 컬렉션을 만드는 파이썬 문법입니다.")
                    elif isinstance(node, ast.IfExp):
                        add_syn("삼항 조건식 (`A if 조건 else B`)", "조건이 참이면 왼쪽 값 `A`, 거짓이면 오른쪽 값 `B` 를 선택하는 한 줄 식입니다.")
                    elif isinstance(node, ast.Subscript) and isinstance(node.slice, ast.Slice):
                        add_syn("슬라이싱 (`x[시작:끝]`)", "리스트·문자열의 일부 구간만 잘라서 새 시퀀스로 꺼냅니다 (`[:i+1]`은 처음부터 `i`번까지).")
                    elif isinstance(node, ast.JoinedStr):
                        add_syn("f-문자열 (`f\"...{변수}...\"`)", "문자열 안의 `{}` 자리에 변수 값이나 계산 결과를 바로 끼워 넣습니다.")
                    elif isinstance(node, ast.Assign) and isinstance(node.targets[0], (ast.Tuple, ast.List)):
                        add_syn("언패킹 대입 (`a, b = ...`)", "튜플이나 리스트의 원소를 순서대로 여러 변수에 한 번에 나눠 담습니다.")
                    elif isinstance(node, ast.Lambda):
                        add_syn("람다 (`lambda 인자: 식`)", "`def`로 이름을 붙이지 않고 일회용 짧은 함수를 즉석에서 만듭니다.")
                    elif isinstance(node, (ast.Try, getattr(ast, "TryStar", ast.Try))):
                        add_syn("예외 처리 (`try / except`)", "`try` 안을 실행하다 오류가 나도 프로그램이 죽지 않고 `except` 블록으로 건너뛰어 처리합니다.")
                    elif isinstance(node, (ast.With, ast.AsyncWith)):
                        add_syn("컨텍스트 매니저 (`with ... as ...`)", "파일·잠금 등을 블록 동안만 열고, 블록이 끝나면(오류가 나도) 자동으로 닫아줍니다.")
                    elif isinstance(node, ast.BoolOp):
                        add_syn("논리 연산 (`and` / `or` 단락 평가)", "`and`는 거짓이 나오면 멈추고, `or`는 참(비어있지 않은 값)이 나오는 첫 값을 돌려줍니다.")
                    elif isinstance(node, (ast.Yield, ast.YieldFrom)):
                        add_syn("제너레이터 (`yield`)", "결과를 한꺼번에 반환하지 않고, 요청할 때마다 하나씩 꺼내주는 이터레이터를 만듭니다.")
                    elif isinstance(node, ast.Call):
                        if isinstance(node.func, ast.Name) and node.func.id in ("enumerate", "zip", "isinstance", "getattr", "setdefault"):
                            add_syn(f"내장/주요 함수 `{node.func.id}()`", KB_CALLS.get(node.func.id) or KB_METHODS.get(node.func.id, ""))
            else:
                sl = "\n".join(fr.lines[ln - 1] for ln in range(max(1, l1), min(l2, len(fr.lines)) + 1))
                if fr.lang in ("js", "ts", "tsx"):
                    if "=>" in sl:
                        add_syn("화살표 함수 (`(인자) => ...`)", "짧은 익명 함수를 만들고, 바깥의 `this` 문맥을 그대로 유지하는 JS/TS 문법입니다.")
                    if re.search(r"\b(?:async|await)\b", sl):
                        add_syn("비동기 처리 (`async / await`)", "서버 통신이나 파일 읽기처럼 시간이 걸리는 Promise 작업이 끝날 때까지 기다린 뒤 다음 줄로 진행합니다.")
                    if re.search(r"\b(?:const|let)\b", sl):
                        add_syn("블록 변수 선언 (`const` / `let`)", "`const`는 재대입 금지 상수(참조 고정), `let`은 값이 바뀔 수 있는 블록 범위 변수입니다.")
                    if re.search(r"(?:\{[^}\n]+\}|\[[^\]\n]+\])\s*=", sl):
                        add_syn("구조 분해 할당 (`{ a, b } = obj`)", "객체 속성이나 배열 원소를 꺼내 같은 이름의 변수로 한 번에 펼칩니다.")
                    if "?." in sl or "??" in sl:
                        add_syn("안전 접근/기본값 (`?.` / `??`)", "`?.`는 값이 `null`/`undefined`여도 오류 없이 멈추고, `??`는 null/undefined일 때만 오른쪽 기본값을 씁니다.")
                    if re.search(r"`[^`]*\$\{", sl):
                        add_syn("템플릿 리터럴 (`` `...${변수}` ``)", "백틱 안에서 `${}`로 변수 값이나 식을 문자열에 바로 끼워 넣습니다.")
                    if re.search(r"\b(?:interface|type)\s+[A-Z]", sl) or (fr.lang in ("ts", "tsx") and re.search(r":\s*(?:string|number|boolean|any|unknown|void|Promise<|Array<)", sl)):
                        add_syn("TypeScript 타입 표기 (`: Type` / `interface`)", "변수·인자·반환값의 자료형 모양을 미리 적어 실행 전에 오타나 타입 불일치를 잡아줍니다.")
                    if re.search(r"\b(?:try|catch)\b", sl):
                        add_syn("예외 처리 (`try / catch`)", "`try` 안을 실행하다 예외가 발생하면 프로그램이 멈추지 않고 `catch` 블록에서 복구합니다.")
                    if re.search(r"\b(?:import|export)\b", sl):
                        add_syn("ES 모듈 (`import / export`)", "다른 파일의 함수·변수를 가져오거나(`import`) 현재 파일의 대상을 외부에 공개(`export`)합니다.")
                elif fr.lang in ("c", "cpp"):
                    if re.search(r"^\s*#include", sl, re.M):
                        add_syn("헤더 포함 (`#include`)", "다른 `.h`/`.hpp` 파일이나 표준 라이브러리의 함수·구조체 선언을 컴파일 전에 불러옵니다.")
                    if "::" in sl:
                        add_syn("범위 지정 연산자 (`네임스페이스::이름`)", "`std::vector`나 `Class::method`처럼 소속 네임스페이스·클래스 안의 대상을 가리킵니다.")
                    if "->" in sl:
                        add_syn("포인터 멤버 접근 (`ptr->member`)", "주소를 가리키는 포인터 `ptr`이 참조하는 실제 구조체/객체의 멤버에 접근합니다 (`(*ptr).member`와 같음).")
                    if re.search(r"\btemplate\s*<", sl):
                        add_syn("템플릿 (`template <typename T>`)", "자료형(`int`, `double` 등)을 고정하지 않고 호출 시점에 맞춰 코드를 자동 생성하는 제네릭 문법입니다.")
                    if re.search(r"\b(?:class|struct|namespace)\b", sl):
                        add_syn("사용자 정의 타입 (`struct` / `class` / `namespace`)", "관련된 데이터와 메서드를 한 덩어리로 묶거나 이름 충돌을 막기 위해 영역을 나눕니다.")
                    if re.search(r"(?:\b(?:const\s+)?(?:void|int|char|float|double|long|short|auto|bool|size_t|uint\w+|int\w+)\s*[*&]+\s*[A-Za-z_]\w*|(?<=[(,=])\s*[*&][A-Za-z_]\w*)", sl):
                        add_syn("포인터·참조 (`*` / `&`)", "값 복사 대신 메모리 주소(`*`)나 별명(`&`)을 넘겨 큰 데이터를 효율적으로 다루거나 원본을 직접 바꿉니다.")
                    if re.search(r"\b(?:new|delete|malloc|free|sizeof)\b", sl):
                        add_syn("동적 메모리·크기 (`new`/`delete`, `malloc`/`free`)", "실행 중 필요한 만큼 힙 메모리를 할당·해제하거나 자료형의 바이트 크기(`sizeof`)를 구합니다.")
                elif fr.lang == "matlab":
                    if re.search(r"\bfunction\b", sl):
                        add_syn("MATLAB 함수 선언 (`function [out] = name(in)`)", "여러 개의 반환값을 `[y1, y2]`처럼 대괄호에 나열해 돌려줄 수 있는 MATLAB 함수 형식입니다.")
                    if re.search(r"\.(?:\*|/|\^|\\)", sl):
                        add_syn("요소별(element-wise) 연산 (`.*` `./` `.^`)", "행렬 곱셈(`*`)과 달리 같은 위치의 원소끼리 하나씩 계산합니다(벡터·이미지 처리에서 자주 씀).")
                    if re.search(r"\[[^\]]+\]", sl):
                        add_syn("행렬·벡터 리터럴 (`[a, b; c, d]`)", "공백/쉼표로 열을, 세미콜론(`;`)으로 행을 구분해 행렬을 만들거나 이어 붙입니다.")
                    if re.search(r"\bparfor\b", sl):
                        add_syn("병렬 반복 (`parfor`)", "각 반복이 서로 독립적일 때 여러 CPU 코어에 작업을 나눠 동시에 실행합니다.")
                    if re.search(r"\bend\b", sl):
                        add_syn("`end` (마지막 인덱스 또는 블록 종료)", "`if`/`for`/`function` 블록을 닫거나, `x(1:end-1)`처럼 배열의 마지막 원소 위치를 뜻합니다.")
                    if re.search(r"@(?:\(|[A-Za-z_])", sl):
                        add_syn("함수 핸들·익명 함수 (`@(x) ...` / `@func`)", "함수를 값처럼 변수에 담거나 `arrayfun`/`ode45` 등에 인자로 넘길 때 씁니다.")
                    if "'" in sl or ".'" in sl:
                        add_syn("전치 연산자 (`'` / `.'`)", "행과 열을 뒤집는 전치 행렬 연산입니다 (`'`는 복소수 켤레 전치, `.'`는 단순 전치).")
                for c in ctx["ext_info"]:
                    mean = c.get("meaning") or ""
                    if mean:
                        add_syn(f"주요 함수/도구 `{c['name']}`", mean)

            if not found:
                add_syn(f"기본 {lang_nm} 구문", f"변수 대입, 조건 분기, 함수 호출 등 기본 {lang_nm} 문법으로 구성되어 있습니다.")
            ans = f"**{lang_ico} 이 구간에 쓰인 {lang_nm} 문법 풀이**\n" + "\n".join(f"- **{k}**: {v}" for k, v in found[:6])
            return ans, [s for s in suggs if s["mode"] != "syntax"]

        # mode == "chat": 사용자 자유 질문에 대한 정적 문맥 응답
        q_toks = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", question))
        var_focus = str(ctx.get("var_name", "") or "").strip()
        if var_focus:
            q_toks.add(var_focus)
        matched_vars = [v for k, v in u.vars.items() if k in q_toks or k.split(".")[-1] in q_toks]
        matched_callees = [c for c in ctx["callees_info"] if c["name"].split(".")[-1] in q_toks or c["name"] in question]
        parts: List[str] = []
        if matched_vars:
            parts.append("**🔎 질문하신 변수 분석**")
            for v in matched_vars[:4]:
                defs = ", ".join(f"L{d[0]}(`{d[1]}`)" for d in v.get("defs", [])[:3]) or "-"
                uses = ", ".join(f"L{x}" for x in sorted(set(v.get("uses", [])))[:6]) or "사용 없음"
                parts.append(f"- `{v['name']}` ({v['kind']}, 추정 타입 `{v['type'] or '?'}`): 정의 {defs} → 사용 {uses}")
        if matched_callees:
            parts.append("**📞 질문하신 호출 함수 분석**")
            for c in matched_callees[:3]:
                parts.append(f"- `{c['sig']}` ({c['loc']}): {c['one']}")
        if any(w in question for w in ("왜", "이유", "목적", "역할")):
            why_txt, _ = self._static_answer(ctx, question, "why", level)
            parts.append(why_txt)
        elif any(w in question for w in ("예시", "값", "추적", "어떻게 변")):
            tr_txt, _ = self._static_answer(ctx, question, "trace", level)
            parts.append(tr_txt)
        elif any(w in question for w in ("문법", "뜻", "의미")):
            syn_txt, _ = self._static_answer(ctx, question, "syntax", level)
            parts.append(syn_txt)
        if not parts:
            brief = self._static_brief(ctx, level)
            parts.append(f"**📘 L{l1}–L{l2} 맥락 기반 설명**\n{brief['intent']}\n\n" + "\n".join(f"- {f}" for f in brief["flow"][:4]))
        parts.append("\n> 💡 *현재 정적 맥락 튜터 모드입니다. 상단 `⚙ LLM 설정`에서 내부망/로컬 LLM API를 연결하면 자유 질문에 대해 AI가 코드를 읽고 더 유연하게 1:1 대답을 해줍니다.*")
        return "\n".join(parts), suggs

    def answer_question(self, uid: int, file_id: int, l1: int, l2: int, question: str,
                        mode: str = "chat", level: str = "beginner", var_name: str = "") -> Dict[str, Any]:
        ctx = self.build_block_context(uid, file_id, l1, l2)
        if var_name:
            ctx["var_name"] = var_name
        u = ctx["u"]
        q_clean = (question or "").strip() or "이 구간을 쉽게 설명해 줘"
        refs = self._wiki_refs(ctx, q_clean)
        ts = time.strftime("%m/%d %H:%M")
        user_msg = {"id": sha1(f"u|{time.time()}|{q_clean}")[:10], "role": "user",
                    "range": [ctx["l1"], ctx["l2"]], "q": q_clean, "mode": mode, "ts": ts}

        with self.lock:
            prev_msgs = list(self.state["threads"].get(str(u.id), []))

        ans_text = ""
        source = "static"
        model_used = ""
        suggs = self._suggestions(ctx)

        if self.cfg.get("use_llm") and self.cfg.get("base_url"):
            cl = self._client()
            if not cl.model:
                try:
                    ids = cl.list_models()
                    if ids:
                        cl.model = ids[0]
                except Exception:
                    pass
            if cl.model:
                lang_nm = LANG_LABELS.get(ctx["fr"].lang, "프로그래밍")
                mode_hint = {
                    "trace": "구체적인 예시 값을 가정하여 변수가 단계마다 어떻게 바뀌는지 실행 흐름을 추적해 설명하라.",
                    "why": "이 구간이 왜 필요한지, 앞선 데이터와 뒤쪽 흐름/호출자와 어떻게 이어지는지 설명하라.",
                    "connect": "이 함수를 부르는 상위 맥락과 이 구간이 호출하는 하위 함수들의 역할을 연결해 설명하라.",
                    "syntax": f"이 구간에 사용된 {lang_nm} 문법과 관용 표현을 초보자가 이해하기 쉽게 비유와 함께 풀어 설명하라.",
                }.get(mode, "초보자 질문에 친절하고 구체적으로 답하라.")
                msgs: List[Dict[str, str]] = [{"role": "system", "content": TUTOR_SYS_PROMPT}]
                var_ctx = ""
                if var_name and var_name in u.vars:
                    vv = u.vars[var_name]
                    vdefs = ", ".join(f"L{d[0]}" for d in vv.get("defs", [])[:5]) or "-"
                    vuses = ", ".join(f"L{x}" for x in sorted(set(vv.get("uses", [])))[:8]) or "-"
                    var_ctx = f"\n[현재 추적 중인 변수] `{var_name}` (종류: {vv.get('kind')}, 정의: {vdefs}, 사용: {vuses})"
                msgs.append({"role": "user", "content": "[현재 코드 및 정적 맥락]\n" + self._ctx_prompt_block(ctx) + var_ctx + self._format_wiki_prompt(refs)})
                for pm in prev_msgs[-6:]:
                    if pm.get("role") == "user":
                        msgs.append({"role": "user", "content": pm.get("q", "")})
                    elif pm.get("role") == "assistant":
                        msgs.append({"role": "assistant", "content": short(pm.get("text", ""), 900)})
                msgs.append({"role": "user", "content": f"[질문 (구간 L{ctx['l1']}-L{ctx['l2']})]\n{q_clean}\n\n[튜터링 지침] {mode_hint}"})
                try:
                    raw, finish = cl.complete_messages(msgs, max_tokens=2400, temperature=0.25)
                    ans_text = clean_llm_text(raw, keep_md=True)
                    if finish == "length" and ans_text:
                        ans_text += "\n\n*(⚠ 모델 출력 토큰 제한(`max_tokens`)으로 뒷부분이 잘렸을 수 있습니다. \"이어서 설명해 줘\"라고 입력하면 계속 답합니다.)*"
                    source = "llm"
                    model_used = cl.model
                except Exception as e:
                    st_ans, suggs = self._static_answer(ctx, q_clean, mode, level)
                    ans_text = st_ans + f"\n\n*(LLM 호출 실패로 정적 맥락 답변을 표시했습니다: {e})*"

        if not ans_text:
            ans_text, suggs = self._static_answer(ctx, q_clean, mode, level)

        titles = {"trace": "💡 예시 값 실행 추적", "why": "🧩 존재 이유와 맥락",
                  "connect": "🔗 함수·데이터 연결", "syntax": "🐍 파이썬 문법 풀이"}
        asst_msg = {
            "id": sha1(f"a|{time.time()}|{ans_text[:40]}")[:10],
            "role": "assistant",
            "range": [ctx["l1"], ctx["l2"]],
            "title": titles.get(mode, "💬 1:1 튜터 답변"),
            "text": ans_text,
            "source": source,
            "model": model_used,
            "suggestions": suggs[:3],
            "refs": refs,
            "ts": ts,
        }
        with self.lock:
            th = self.state["threads"].setdefault(str(u.id), [])
            th.extend([user_msg, asst_msg])
            if len(th) > 40:
                self.state["threads"][str(u.id)] = th[-40:]
            self._save_state()
            cur_th = list(self.state["threads"][str(u.id)])
        return {"ok": True, "user_msg": user_msg, "assistant_msg": asst_msg, "thread": cur_th}

    def pin(self, uid: int, action: str, pin_id: str = "", title: str = "",
            text: str = "", rng: Optional[list] = None) -> Dict[str, Any]:
        with self.lock:
            plist = self.state["pins"].setdefault(str(uid), [])
            if action == "remove":
                self.state["pins"][str(uid)] = [p for p in plist if p.get("id") != pin_id]
            else:
                pid = pin_id or sha1(f"pin|{uid}|{text[:60]}")[:10]
                if not any(p.get("id") == pid for p in plist):
                    plist.append({
                        "id": pid, "title": short(title or "고정 노트", 50),
                        "text": text, "range": rng or [], "ts": time.strftime("%m/%d %H:%M"),
                    })
            self._save_state()
            return {"ok": True, "pins": list(self.state["pins"].get(str(uid), []))}

    def clear_thread(self, uid: int) -> Dict[str, Any]:
        with self.lock:
            self.state["threads"][str(uid)] = []
            self._save_state()
            return {"ok": True, "thread": []}

    def delete_msg(self, uid: int, msg_id: str) -> Dict[str, Any]:
        mid = str(msg_id or "").strip()
        with self.lock:
            th = list(self.state["threads"].get(str(uid), []))
            idx = next((i for i, m in enumerate(th) if str(m.get("id", "")) == mid), -1)
            if idx >= 0:
                if idx > 0 and th[idx - 1].get("role") == "user":
                    del th[idx - 1:idx + 1]
                else:
                    del th[idx]
                self.state["threads"][str(uid)] = th
                self._save_state()
            return {"ok": True, "thread": th}


def create_tutor_server(proj: Project, out_html: Path, cfg: Dict[str, Any], port: int = 8765,
                        fallback_port: bool = False) -> Tuple[ThreadingHTTPServer, str]:
    state_box: Dict[str, Any] = {
        "engine": TutorEngine(proj, cfg, out_html),
        "out_html": out_html,
        "cfg": dict(cfg),
        "lock": threading.Lock(),
    }

    def switch_project(target_path: str, reanalyze: bool = False) -> Dict[str, Any]:
        raw = (target_path or "").strip().strip('"')
        if not raw:
            return {"ok": False, "error": "폴더 경로가 비어 있습니다."}
        target = Path(raw).resolve()
        if not target.is_dir():
            return {"ok": False, "error": f"존재하지 않는 폴더입니다: {target}"}
        with state_box["lock"]:
            old_eng: TutorEngine = state_box["engine"]
            old_eng.prewarm["stop"] = True
            cur_cfg = dict(state_box["cfg"])
            cur_cfg.update({k: v for k, v in load_config().items() if k in ("use_llm", "base_url", "api_key", "model", "extra_body", "workers", "max_calls", "timeout")})
            cur_cfg["last_dir"] = str(target)
            save_config(cur_cfg)
            proj_box: List[Project] = []
            new_out = run_pipeline(
                target, use_llm=False, open_browser=False,
                timeout=int(cur_cfg.get("timeout", 90) or 90),
                log=lambda _m: None, _proj_out=proj_box,
            )
            new_eng = TutorEngine(proj_box[0], cur_cfg, new_out)
            state_box["engine"] = new_eng
            state_box["out_html"] = new_out
            state_box["cfg"] = cur_cfg
            return {"ok": True, "url": f"/{new_out.name}", "root": str(target)}

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, fmt: str, *args: Any) -> None:
            return

        def _send(self, code: int, ctype: str, body: bytes) -> None:
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def _send_json(self, code: int, obj: Any) -> None:
            self._send(code, "application/json; charset=utf-8", json.dumps(obj, ensure_ascii=False).encode("utf-8"))

        def _read_json(self) -> Dict[str, Any]:
            n = int(self.headers.get("Content-Length", "0") or 0)
            raw = self.rfile.read(n) if n > 0 else b"{}"
            try:
                v = json.loads(raw.decode("utf-8", "replace"))
                return v if isinstance(v, dict) else {}
            except Exception:
                return {}

        def do_GET(self) -> None:
            path = urllib.parse.unquote(urllib.parse.urlparse(self.path).path)
            eng: TutorEngine = state_box["engine"]
            cur_html: Path = state_box["out_html"]
            if path in ("/", f"/{cur_html.name}"):
                try:
                    self._send(200, "text/html; charset=utf-8", cur_html.read_bytes())
                except OSError as e:
                    self._send(500, "text/plain; charset=utf-8", str(e).encode("utf-8"))
                return
            if path == "/api/status":
                self._send_json(200, eng.status_payload())
                return
            if path == "/api/projects":
                self._send_json(200, {"ok": True, "current_root": str(eng.proj.root), "projects": list_workspace_projects(eng.proj.root)})
                return
            if path == "/api/wiki/status":
                self._send_json(200, {"ok": True, "wiki": eng.wiki.status()})
                return
            if path == "/api/wiki/doc":
                qs = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
                did = (qs.get("id") or [""])[0]
                doc = eng.wiki.get_doc(did)
                if doc:
                    self._send_json(200, {"ok": True, "doc": doc})
                else:
                    self._send_json(404, {"ok": False, "error": "문서를 찾을 수 없습니다."})
                return
            self._send(404, "text/plain; charset=utf-8", b"Not Found")

        def do_POST(self) -> None:
            path = urllib.parse.urlparse(self.path).path
            body = self._read_json()
            eng: TutorEngine = state_box["engine"]
            try:
                if path == "/api/config":
                    res = eng.update_config(body)
                    state_box["cfg"].update(eng.cfg)
                    self._send_json(200, res)
                elif path == "/api/brief":
                    res = eng.brief(
                        int(body.get("unit_id", 0)), int(body.get("file_id", 0)),
                        int(body.get("l1", 0)), int(body.get("l2", 0)),
                        str(body.get("level", "beginner")), bool(body.get("force", False)),
                    )
                    self._send_json(200, res)
                elif path == "/api/chat":
                    res = eng.answer_question(
                        int(body.get("unit_id", 0)), int(body.get("file_id", 0)),
                        int(body.get("l1", 0)), int(body.get("l2", 0)),
                        str(body.get("question", "")), str(body.get("mode", "chat")),
                        str(body.get("level", "beginner")), str(body.get("var_name", "")),
                    )
                    self._send_json(200, res)
                elif path == "/api/pin":
                    res = eng.pin(
                        int(body.get("unit_id", 0)), str(body.get("action", "add")),
                        str(body.get("pin_id", "")), str(body.get("title", "")),
                        str(body.get("text", "")), body.get("range"),
                    )
                    self._send_json(200, res)
                elif path == "/api/clear_thread":
                    self._send_json(200, eng.clear_thread(int(body.get("unit_id", 0))))
                elif path == "/api/delete_msg":
                    self._send_json(200, eng.delete_msg(int(body.get("unit_id", 0)), str(body.get("msg_id", ""))))
                elif path == "/api/prewarm":
                    act = str(body.get("action", "start"))
                    if act == "stop":
                        eng.prewarm["stop"] = True
                        self._send_json(200, {"ok": True, "prewarm": dict(eng.prewarm)})
                    else:
                        self._send_json(200, eng.start_prewarm(int(body.get("max_items", 0) or 0)))
                elif path == "/api/study_state":
                    self._send_json(200, eng.update_study_state(body))
                elif path == "/api/project_switch":
                    self._send_json(200, switch_project(str(body.get("path", "")), bool(body.get("reanalyze", False))))
                elif path == "/api/project_browse":
                    picked = _pick_directory_dialog(str(eng.proj.root.parent))
                    self._send_json(200, {"ok": bool(picked), "path": picked})
                elif path == "/api/project_remove":
                    ws_id = str(body.get("ws_id", "")).strip()
                    ws_dir = (WORKSPACES_ROOT / ws_id).resolve() if ws_id else None
                    if ws_dir and ws_dir.parent == WORKSPACES_ROOT.resolve() and ws_dir.is_dir():
                        shutil.rmtree(ws_dir, ignore_errors=True)
                    self._send_json(200, {"ok": True})
                elif path == "/api/wiki/index":
                    act = str(body.get("action", "scan"))
                    if act == "browse_dir":
                        picked = _pick_directory_dialog(str(eng.proj.root), "논문/참고 문서 폴더 선택")
                        res = eng.wiki.add_sources([picked]) if picked else {"ok": False, "cancelled": True, "status": eng.wiki.status()}
                        self._send_json(200, res)
                    elif act == "browse_files":
                        picked_list = _pick_paper_files_dialog(str(eng.proj.root))
                        res = eng.wiki.add_sources(picked_list) if picked_list else {"ok": False, "cancelled": True, "status": eng.wiki.status()}
                        self._send_json(200, res)
                    elif act == "add_path":
                        p_str = str(body.get("path", "")).strip()
                        res = eng.wiki.add_sources([p_str]) if p_str else {"ok": False, "error": "경로가 비어 있습니다.", "status": eng.wiki.status()}
                        self._send_json(200, res)
                    elif act == "remove_source":
                        res = eng.wiki.remove_source(str(body.get("path", "")))
                        self._send_json(200, res)
                    elif act == "build_llm":
                        if not eng.cfg.get("use_llm") or not eng.cfg.get("base_url"):
                            self._send_json(200, {"ok": False, "error": "LLM이 활성화되어 있지 않습니다. 먼저 ⚙ LLM 설정에서 연결하세요.", "status": eng.wiki.status()})
                        else:
                            cl = eng._client()
                            if not cl.model:
                                try:
                                    ids = cl.list_models()
                                    if ids:
                                        cl.model = ids[0]
                                except Exception:
                                    pass
                            if not cl.model:
                                self._send_json(200, {"ok": False, "error": "LLM 모델명이 설정되지 않았습니다.", "status": eng.wiki.status()})
                            else:
                                self._send_json(200, eng.wiki.build_llm_wiki(cl, force=bool(body.get("force", False))))
                    else:
                        self._send_json(200, eng.wiki.scan(force=bool(body.get("force", False))))
                elif path == "/api/wiki/translate":
                    self._send_json(200, eng.translate_wiki_snippet(str(body.get("text", ""))))
                elif path == "/api/wiki/open":
                    self._send_json(200, eng.open_wiki_doc(str(body.get("doc_id", ""))))
                elif path == "/api/shutdown":
                    self._send_json(200, {"ok": True})
                    srv_ref = state_box.get("srv")
                    if srv_ref is not None:
                        threading.Thread(target=srv_ref.shutdown, daemon=True).start()
                else:
                    self._send_json(404, {"ok": False, "error": "Unknown endpoint"})
            except Exception as e:
                self._send_json(500, {"ok": False, "error": str(e)})

    try:
        srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    except OSError:
        if not fallback_port:
            raise
        srv = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
    state_box["srv"] = srv
    actual_port = srv.server_address[1]
    url = f"http://127.0.0.1:{actual_port}/{out_html.name}"
    return srv, url


def _find_preferred_browser() -> Optional[str]:
    """시스템 기본 브라우저(예: IE)와 무관하게 Chrome → Edge 순으로 실행 파일 경로를 찾는다."""
    if os.name == "nt":
        cands: List[Path] = []
        for env_k, sub in (
            ("PROGRAMFILES", "Google/Chrome/Application/chrome.exe"),
            ("PROGRAMFILES(X86)", "Google/Chrome/Application/chrome.exe"),
            ("LOCALAPPDATA", "Google/Chrome/Application/chrome.exe"),
        ):
            base = os.environ.get(env_k, "")
            if base:
                cands.append(Path(base) / sub)
        for p in cands:
            if p.is_file():
                return str(p)
        for cmd in ("chrome", "chrome.exe"):
            found = shutil.which(cmd)
            if found:
                return found
        try:
            import winreg  # type: ignore
            for exe_name in ("chrome.exe", "msedge.exe"):
                for root_h in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
                    try:
                        with winreg.OpenKey(root_h, rf"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\{exe_name}") as k:
                            val, _ = winreg.QueryValueEx(k, "")
                            if val:
                                pval = str(val).strip().strip('"')
                                if pval and Path(pval).is_file():
                                    return pval
                    except OSError:
                        pass
        except Exception:
            pass
        for env_k, sub in (
            ("PROGRAMFILES(X86)", "Microsoft/Edge/Application/msedge.exe"),
            ("PROGRAMFILES", "Microsoft/Edge/Application/msedge.exe"),
            ("LOCALAPPDATA", "Microsoft/Edge/Application/msedge.exe"),
        ):
            base = os.environ.get(env_k, "")
            if base and (Path(base) / sub).is_file():
                return str(Path(base) / sub)
        for cmd in ("msedge", "msedge.exe"):
            found = shutil.which(cmd)
            if found:
                return found
    else:
        mac_chrome = Path("/Applications/Google Chrome.app/Contents/MacOS/Google Chrome")
        if mac_chrome.is_file():
            return str(mac_chrome)
        for cmd in ("google-chrome", "chromium", "chromium-browser", "microsoft-edge"):
            found = shutil.which(cmd)
            if found:
                return found
    return None


def open_preferred_browser(url: str) -> str:
    """가능하면 Chrome(없으면 Edge)으로 열고, 둘 다 없으면 기본 브라우저로 연다."""
    exe = _find_preferred_browser()
    if exe:
        try:
            subprocess.Popen([exe, url], close_fds=True)
            return Path(exe).name
        except Exception:
            pass
    try:
        webbrowser.open(url)
    except Exception:
        pass
    return "default"


def serve_app(proj: Project, out_html: Path, cfg: Dict[str, Any], port: int = 8765,
              open_browser: bool = True, log: Callable[[str], None] = print) -> None:
    srv, url = create_tutor_server(proj, out_html, cfg, port=port, fallback_port=False)
    log(f"[서버] 1:1 Code Tutor 서버 실행 중: {url}  (종료: Ctrl+C)")
    if open_browser:
        b = open_preferred_browser(url)
        log(f"[브라우저] {b} 로 열었습니다: {url}")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        srv.server_close()


def run_pipeline(root: Path, out_html: Optional[Path] = None, use_llm: bool = False, base_url: str = "",
                 api_key: str = "", model: str = "", workers: int = 2, max_calls: int = 150,
                 timeout: int = 90, extra_body: Optional[dict] = None, excludes: Optional[set] = None,
                 refresh: bool = False, open_browser: bool = True,
                 log: Callable[[str], None] = print,
                 progress: Optional[Callable[[str, int, int], None]] = None,
                 _proj_out: Optional[List[Project]] = None) -> Path:
    t0 = time.time()
    root = Path(root).resolve()
    log(f"[1/3] 정적 분석: {root}")
    proj = Project(root, excludes, log=log)
    proj.analyze(progress)
    if _proj_out is not None:
        _proj_out.append(proj)
    funcs = len([u for u in proj.units if u.kind == "function"])
    log(f"  -> 파일 {len(proj.files)}개 · 함수/메서드 {funcs}개 · 호출 관계 {sum(len(u.callees) for u in proj.units)}개")
    if proj.errors:
        log(f"  -> 일부 문장 분석 실패 {len(proj.errors)}건 (해당 줄은 기본 해설로 표시): {proj.errors[0]}")

    ws_dir = get_project_workspace_dir(root)
    ai_stats: dict = {"enabled": False, "model": "", "stopped": ""}
    ai_overview = None
    if use_llm:
        log("[2/3] AI 해설 (선택 기능 · 실패해도 정적 해설은 그대로 유지)")
        cache_path = ws_dir / "llm_cache.json"
        if refresh and cache_path.exists():
            try:
                cache_path.unlink()
            except OSError:
                pass
        client = LLMClient(base_url, api_key, model, timeout, extra_body)
        enr = AIEnricher(proj, client, LLMCache(cache_path), workers, max_calls, log, progress)
        ai_stats = enr.run()
        ai_overview = enr.overview
    else:
        log("[2/3] AI 해설 건너뜀 (정적 분석 모드)")

    log("[3/3] HTML 생성")
    out = out_html or (ws_dir / f"{root.name}_code_tutor.html")
    data, fdata = export_all(proj, ai_stats, ai_overview, root.name)
    out.write_text(build_html(data, fdata), encoding="utf-8")
    log(f"  -> 완료 ({time.time() - t0:.1f}초): {out}  ({out.stat().st_size / 1024:.0f} KB)")
    log(f"  -> 저장 작업폴더 (원본 코드 폴더 수정 없음): {ws_dir}")
    if open_browser:
        open_preferred_browser(out.resolve().as_uri())
    return out


def parse_extra_body(s: str) -> dict:
    s = (s or "").strip()
    if not s:
        return {}
    try:
        v = json.loads(s)
        return v if isinstance(v, dict) else {}
    except json.JSONDecodeError:
        print("[경고] --extra-body 는 JSON 객체여야 합니다. 무시합니다.", file=sys.stderr)
        return {}


def launch_gui() -> None:
    try:
        import tkinter as tk
        from tkinter import filedialog, messagebox, ttk
    except ImportError:
        print("tkinter 를 사용할 수 없습니다. CLI 로 실행하세요: python code_tutor.py <폴더>", file=sys.stderr)
        sys.exit(1)

    cfg = load_config()
    root = tk.Tk()
    root.title(f"Code Tutor v{VERSION}")
    root.geometry("760x640")
    root.minsize(660, 560)

    v_dir = tk.StringVar(value=cfg.get("last_dir", ""))
    v_serve = tk.BooleanVar(value=bool(cfg.get("serve_mode", True)))
    v_port = tk.StringVar(value=str(cfg.get("port", 8765)))
    v_llm = tk.BooleanVar(value=bool(cfg.get("use_llm")))
    v_url = tk.StringVar(value=cfg.get("base_url", ""))
    v_model = tk.StringVar(value=cfg.get("model", ""))
    v_key = tk.StringVar(value=cfg.get("api_key", ""))
    v_workers = tk.StringVar(value=str(cfg.get("workers", 2)))
    v_calls = tk.StringVar(value=str(cfg.get("max_calls", 150)))
    v_extra = tk.StringVar(value=cfg.get("extra_body", ""))
    v_refresh = tk.BooleanVar(value=False)
    active_srv: List[Optional[ThreadingHTTPServer]] = [None]

    main = ttk.Frame(root, padding=14)
    main.pack(fill=tk.BOTH, expand=True)
    ttk.Label(main, text="Code Tutor — 코드 학습용 정적 분석 + 1:1 튜터", font=("Malgun Gothic", 12, "bold")).pack(anchor="w")
    ttk.Label(main, text="폴더를 선택해 실행하면 논리 블록(Step) 해설과 1:1 질문 웹 UI가 열립니다 (폐쇄망 OK).",
              foreground="#475569").pack(anchor="w", pady=(0, 8))

    f1 = ttk.LabelFrame(main, text="1. 분석할 프로젝트 폴더 및 실행 방식", padding=8)
    f1.pack(fill=tk.X, pady=4)
    f1_top = ttk.Frame(f1)
    f1_top.pack(fill=tk.X)
    ttk.Entry(f1_top, textvariable=v_dir).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))

    def browse() -> None:
        d = filedialog.askdirectory(title="분석할 폴더")
        if d:
            v_dir.set(d)
    ttk.Button(f1_top, text="찾아보기…", command=browse).pack(side=tk.RIGHT)

    f1_bot = ttk.Frame(f1)
    f1_bot.pack(fill=tk.X, pady=(6, 0))
    ttk.Checkbutton(f1_bot, text="1:1 대화형 웹 튜터 서버로 실행 (권장 · 브라우저에서 질문/LLM 연동)",
                    variable=v_serve).pack(side=tk.LEFT)
    ttk.Entry(f1_bot, textvariable=v_port, width=7).pack(side=tk.RIGHT)
    ttk.Label(f1_bot, text="포트:").pack(side=tk.RIGHT, padx=(8, 4))

    f2 = ttk.LabelFrame(main, text="2. AI 해설 (선택 · OpenAI 호환 내부망/로컬 LLM)", padding=8)
    f2.pack(fill=tk.X, pady=4)
    ttk.Checkbutton(f2, text="실시간 LLM 튜터 사용 (서버 모드에서는 질문·블록 선택 시 실시간 호출)", variable=v_llm).grid(row=0, column=0, columnspan=4, sticky="w")
    for r, (lab, var, w, show) in enumerate([("Base URL", v_url, 46, ""), ("모델명 (비우면 서버 첫 모델)", v_model, 46, ""),
                                              ("API Key", v_key, 46, "*")], start=1):
        ttk.Label(f2, text=lab).grid(row=r, column=0, sticky="w", pady=2)
        ttk.Entry(f2, textvariable=var, width=w, show=show).grid(row=r, column=1, columnspan=3, sticky="ew", padx=6, pady=2)
    ttk.Label(f2, text="병렬 수").grid(row=4, column=0, sticky="w")
    ttk.Entry(f2, textvariable=v_workers, width=6).grid(row=4, column=1, sticky="w", padx=6)
    ttk.Label(f2, text="최대 호출 수").grid(row=4, column=2, sticky="e")
    ttk.Entry(f2, textvariable=v_calls, width=8).grid(row=4, column=3, sticky="w", padx=6)
    ttk.Label(f2, text="extra_body(JSON)").grid(row=5, column=0, sticky="w", pady=2)
    ttk.Entry(f2, textvariable=v_extra, width=46).grid(row=5, column=1, columnspan=3, sticky="ew", padx=6)
    ttk.Checkbutton(f2, text="캐시 무시하고 다시 요청", variable=v_refresh).grid(row=6, column=0, columnspan=3, sticky="w")
    f2.columnconfigure(1, weight=1)

    ttk.Label(main, text=f"HTML·캐시는 별도 폴더({WORKSPACES_ROOT.name}/)에 저장되어 원본 코드 폴더를 건드리지 않습니다.",
              foreground="#64748b").pack(anchor="w", pady=(0, 6))
    bar = ttk.Progressbar(main, mode="determinate")
    bar.pack(fill=tk.X, pady=(4, 4))
    box = tk.Text(main, height=11, state="disabled", bg="#0f172a", fg="#e2e8f0", font=("Consolas", 9))
    box.pack(fill=tk.BOTH, expand=True)
    btn_row = ttk.Frame(main)
    btn_row.pack(fill=tk.X, pady=(8, 0))

    def open_workspaces() -> None:
        WORKSPACES_ROOT.mkdir(parents=True, exist_ok=True)
        try:
            os.startfile(str(WORKSPACES_ROOT))  # type: ignore[attr-defined]
        except Exception:
            try:
                webbrowser.open(WORKSPACES_ROOT.as_uri())
            except Exception:
                pass

    ttk.Button(btn_row, text="📂 저장 폴더 열기", command=open_workspaces).pack(side=tk.LEFT)
    run_btn = ttk.Button(btn_row, text="▶ 분석하고 튜터 열기")
    run_btn.pack(side=tk.RIGHT)

    def log(msg: str) -> None:
        def _u() -> None:
            box.configure(state="normal")
            box.insert(tk.END, msg + "\n")
            box.see(tk.END)
            box.configure(state="disabled")
        root.after(0, _u)

    def prog(msg: str, i: int, n: int) -> None:
        def _u() -> None:
            bar["maximum"] = max(1, n)
            bar["value"] = i
        root.after(0, _u)

    def stop_prev_server() -> None:
        srv = active_srv[0]
        if srv is not None:
            active_srv[0] = None
            try:
                srv.shutdown()
                srv.server_close()
            except Exception:
                pass

    def on_run() -> None:
        d = v_dir.get().strip()
        if not d or not Path(d).is_dir():
            messagebox.showerror("폴더 오류", "유효한 프로젝트 폴더를 선택하세요.")
            return
        try:
            workers, calls, port = int(v_workers.get()), int(v_calls.get()), int(v_port.get())
            if not (1 <= port <= 65535):
                raise ValueError
        except ValueError:
            messagebox.showerror("입력 오류", "병렬 수, 최대 호출 수, 포트(1~65535)는 숫자여야 합니다.")
            return
        # 스레드 시작 전에 모든 UI 변수를 읽는다 (tkinter 변수는 스레드 안전하지 않음)
        serve_mode = bool(v_serve.get())
        opts = dict(use_llm=v_llm.get(), base_url=v_url.get().strip(), api_key=v_key.get().strip(),
                    model=v_model.get().strip(), workers=workers, max_calls=calls,
                    extra_body=parse_extra_body(v_extra.get()), refresh=v_refresh.get())
        save_cfg = {"base_url": opts["base_url"], "model": opts["model"], "api_key": opts["api_key"],
                    "use_llm": opts["use_llm"], "last_dir": d, "workers": workers, "max_calls": calls,
                    "timeout": cfg.get("timeout", 90), "extra_body": v_extra.get(),
                    "serve_mode": serve_mode, "port": port}
        save_config(save_cfg)
        run_btn.configure(state="disabled")
        bar["value"] = 0

        def work() -> None:
            err = None
            try:
                stop_prev_server()
                proj_box: List[Project] = []
                pipe_opts = dict(opts)
                if serve_mode:
                    pipe_opts["use_llm"] = False
                out = run_pipeline(
                    Path(d), log=log, progress=prog, timeout=int(cfg.get("timeout", 90)),
                    open_browser=(not serve_mode), _proj_out=proj_box, **pipe_opts,
                )
                if serve_mode and proj_box:
                    srv, url = create_tutor_server(proj_box[0], out, save_cfg, port=port, fallback_port=True)
                    active_srv[0] = srv
                    threading.Thread(target=srv.serve_forever, daemon=True).start()
                    log(f"[서버] 1:1 튜터 서버 실행 중 (이 창을 유지하세요): {url}")
                    b = open_preferred_browser(url)
                    log(f"[브라우저] {b} 로 열었습니다.")
            except Exception as e:
                err = str(e)
                log(f"[오류] {err}")
            root.after(0, lambda: run_btn.configure(state="normal"))
            if err is not None:
                root.after(0, lambda m=err: messagebox.showerror("분석 실패", m))
        threading.Thread(target=work, daemon=True).start()

    def on_close() -> None:
        stop_prev_server()
        root.destroy()

    run_btn.configure(command=on_run)
    root.protocol("WM_DELETE_WINDOW", on_close)
    root.mainloop()


def _try_reuse_running_server(port: int, project_dir: Optional[Path], open_browser: bool) -> bool:
    try:
        with urllib.request.urlopen(f"http://127.0.0.1:{port}/api/status", timeout=1.5) as r:
            if r.status != 200:
                return False
            d = json.loads(r.read().decode("utf-8", "replace"))
            if not isinstance(d, dict) or not d.get("ok"):
                return False
            if d.get("code_hash") != _self_code_hash():
                try:
                    req = urllib.request.Request(
                        f"http://127.0.0.1:{port}/api/shutdown",
                        data=b"{}", headers={"Content-Type": "application/json"}, method="POST",
                    )
                    urllib.request.urlopen(req, timeout=1.5).read()
                except Exception:
                    pass
                for _ in range(25):
                    time.sleep(0.1)
                    try:
                        urllib.request.urlopen(f"http://127.0.0.1:{port}/api/status", timeout=0.3)
                    except Exception:
                        break
                return False
    except Exception:
        return False
    url = f"http://127.0.0.1:{port}/"
    if project_dir is not None:
        try:
            req = urllib.request.Request(
                f"http://127.0.0.1:{port}/api/project_switch",
                data=json.dumps({"path": str(project_dir.resolve())}).encode("utf-8"),
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=60) as r:
                sw = json.loads(r.read().decode("utf-8", "replace"))
                if sw.get("ok") and sw.get("url"):
                    url = f"http://127.0.0.1:{port}{sw['url']}"
        except Exception:
            pass
    if open_browser:
        open_preferred_browser(url)
    return True


def main() -> None:
    ap = argparse.ArgumentParser(description="Code Tutor — 코드 학습용 정적 분석 + 오프라인 튜터 생성기")
    ap.add_argument("project_dir", nargs="?", type=Path, help="분석할 프로젝트 폴더 (생략 시 GUI 또는 --serve 최근 프로젝트)")
    ap.add_argument("--gui", action="store_true", help="GUI 실행")
    ap.add_argument("--out", type=Path, default=None, help="출력 HTML 경로")
    ap.add_argument("--no-llm", action="store_true", help="LLM 없이 정적 분석만 (기본값: 설정 파일의 use_llm 따름)")
    ap.add_argument("--llm", action="store_true", help="LLM 사용 (OpenAI 호환 서버)")
    ap.add_argument("--base-url", default=None)
    ap.add_argument("--model", default=None, help="비우면 서버의 첫 모델 사용")
    ap.add_argument("--api-key", default=None)
    ap.add_argument("--workers", type=int, default=None, help="LLM 병렬 요청 수 (기본 2)")
    ap.add_argument("--max-calls", type=int, default=None, help="LLM 최대 호출 수 (기본 150)")
    ap.add_argument("--timeout", type=int, default=None, help="LLM 요청 시간초과 초 (기본 90)")
    ap.add_argument("--extra-body", default=None, help='서버별 추가 파라미터 JSON, 예: \'{"chat_template_kwargs":{"enable_thinking":false}}\'')
    ap.add_argument("--exclude", default="", help="제외할 폴더명(쉼표 구분)")
    ap.add_argument("--refresh", action="store_true", help="LLM 캐시 무시")
    ap.add_argument("--no-open", action="store_true", help="브라우저를 열지 않음")
    ap.add_argument("--serve", action="store_true", help="1:1 대화형 튜터 웹 서버 실행")
    ap.add_argument("--port", type=int, default=8765, help="웹 서버 포트 (기본 8765)")
    a = ap.parse_args()
    if a.gui or (not a.project_dir and not a.serve):
        launch_gui()
        return
    cfg = load_config()
    target_dir = a.project_dir
    if target_dir is None and a.serve:
        last_d = str(cfg.get("last_dir", "")).strip()
        if last_d and Path(last_d).is_dir():
            target_dir = Path(last_d)
        else:
            existing = [p["root"] for p in list_workspace_projects() if p.get("exists")]
            target_dir = Path(existing[0]) if existing else Path(__file__).resolve().parent
    if target_dir is None or not target_dir.is_dir():
        print("[오류] 유효한 프로젝트 폴더가 아닙니다.", file=sys.stderr)
        sys.exit(1)
    if a.serve and _try_reuse_running_server(a.port, a.project_dir, not a.no_open):
        return
    use_llm = bool(cfg.get("use_llm")) if not (a.llm or a.no_llm) else a.llm
    base_url = a.base_url or cfg.get("base_url", "")
    api_key = a.api_key if a.api_key is not None else cfg.get("api_key", "")
    model = a.model if a.model is not None else cfg.get("model", "")
    extra_str = a.extra_body if a.extra_body is not None else cfg.get("extra_body", "")
    cfg_save = dict(cfg)
    cfg_save["last_dir"] = str(target_dir.resolve())
    save_config(cfg_save)
    proj_box: List[Project] = []
    out = run_pipeline(
        target_dir, a.out, use_llm=(use_llm and not a.serve),
        base_url=base_url, api_key=api_key, model=model,
        workers=a.workers or int(cfg.get("workers", 2)), max_calls=a.max_calls or int(cfg.get("max_calls", 150)),
        timeout=a.timeout or int(cfg.get("timeout", 90)),
        extra_body=parse_extra_body(extra_str),
        excludes={x.strip() for x in a.exclude.split(",") if x.strip()}, refresh=a.refresh,
        open_browser=(not a.no_open) and (not a.serve),
        _proj_out=proj_box,
    )
    if a.serve and proj_box:
        srv_cfg = dict(cfg_save)
        srv_cfg.update({"use_llm": use_llm, "base_url": base_url, "api_key": api_key,
                        "model": model, "extra_body": extra_str})
        serve_app(proj_box[0], out, srv_cfg, port=a.port, open_browser=not a.no_open)


if __name__ == "__main__":
    main()

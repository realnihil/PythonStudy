"""
[1강 & 2강 실습] 토스증권 API 첫 연결 및 액세스 토큰 발급

1. .env 파일에서 API 키(App Key / Secret)를 안전하게 로드합니다.
2. 토스 OAuth2 서버에 액세스 토큰(Access Token) 발급을 요청합니다.
3. 발급받은 토큰을 로컬 캐시(.token_cache.json)에 저장하여 불필요한 중복 발급을 방지합니다.
"""

from __future__ import annotations

import json
import os
import sys
import time
import urllib.parse
import urllib.request
from pathlib import Path

# 윈도우 콘솔 한글 및 이모지 출력 인코딩 설정
if sys.platform == "win32":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
        sys.stderr.reconfigure(encoding="utf-8")
    except Exception:
        pass

# 토스증권 Open API 기본 주소
BASE_URL = "https://openapi.tossinvest.com"

# 프로젝트 루트 경로 (TossInvest_api_study)
BASE_DIR = Path(__file__).resolve().parent.parent.parent
ENV_PATH = BASE_DIR / ".env"
CACHE_PATH = BASE_DIR / ".token_cache.json"

# 토큰 만료 1분 전에는 미리 새로고침하도록 여유 시간 설정 (초 단위)
SAFETY_MARGIN = 60


def load_env(path: Path = ENV_PATH) -> None:
    """
    외부 라이브러리(python-dotenv 등) 없이도 동작하도록
    순수 파이썬 표준 라이브러리로 .env 파일을 읽어 환경 변수로 등록합니다.
    """
    if not path.exists():
        raise FileNotFoundError(f"[경고] .env 파일을 찾을 수 없습니다: {path}")

    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        # 빈 줄과 주석(#)은 무시
        if not line or line.startswith("#") or "=" not in line:
            continue
        # '='를 기준으로 키와 값 분리
        key, value = line.split("=", 1)
        os.environ.setdefault(key.strip(), value.strip().strip('"').strip("'"))


def issue_token(client_id: str, client_secret: str) -> dict:
    """
    토스증권 OAuth2 인증 서버에 client_id와 client_secret을 전송하여
    새로운 액세스 토큰(Access Token)을 발급받습니다.
    """
    url = f"{BASE_URL}/oauth2/token"

    # POST 요청 바디 데이터 구성 (application/x-www-form-urlencoded 형식)
    form_data = urllib.parse.urlencode({
        "grant_type": "client_credentials",
        "client_id": client_id,
        "client_secret": client_secret,
    }).encode("utf-8")

    request = urllib.request.Request(
        url=url,
        data=form_data,
        headers={"Content-Type": "application/x-www-form-urlencoded"},
        method="POST",
    )

    try:
        with urllib.request.urlopen(request, timeout=10) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        err_msg = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"토큰 발급 실패 (HTTP {exc.code}): {err_msg}")

    # 토큰 만료 시점(초 단위 타임스탬프) 계산
    # 보통 토스 API는 expires_in (유효 시간 초)을 함께 반환합니다.
    expires_in = payload.get("expires_in", 86400)  # 기본값 24시간
    expires_at = time.time() + expires_in

    return {
        "access_token": payload["access_token"],
        "token_type": payload.get("token_type", "Bearer"),
        "expires_at": expires_at,
        "issued_at": time.strftime("%Y-%m-%d %H:%M:%S", time.localtime()),
    }


def load_cached_token() -> dict | None:
    """
    로컬에 저장된 토큰 캐시 파일이 유효한지 확인하고,
    아직 만료되지 않았다면 재사용합니다.
    """
    if not CACHE_PATH.exists():
        return None

    try:
        cached = json.loads(CACHE_PATH.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None

    # 만료 시점까지 안전 마진(SAFETY_MARGIN) 이상 남아있는지 체크
    if cached.get("expires_at", 0) - SAFETY_MARGIN <= time.time():
        return None

    return cached


def save_cached_token(token_data: dict) -> None:
    """토큰 데이터를 로컬 파일에 JSON 형태로 저장합니다."""
    CACHE_PATH.write_text(json.dumps(token_data, indent=2, ensure_ascii=False), encoding="utf-8")


def get_access_token() -> str:
    """
    [핵심 함수] 유효한 토큰이 있으면 캐시에서 가져오고, 없으면 새로 발급받습니다.
    """
    # 1. 캐시된 토큰 확인
    cached = load_cached_token()
    if cached:
        print("💡 [캐시 재사용] 기존에 발급받은 유효한 토큰을 불러왔습니다.")
        return cached["access_token"]

    # 2. 캐시가 없거나 만료되었으면 .env 로드 후 새 발급
    print("🔑 [새 토큰 요청] 토스증권 서버에 새 액세스 토큰 발급을 요청합니다...")
    load_env()

    client_id = os.environ.get("TOSS_APP_KEY") or os.environ.get("TOSS_CLIENT_ID")
    client_secret = os.environ.get("TOSS_APP_SECRET") or os.environ.get("TOSS_CLIENT_SECRET")

    if not client_id or not client_secret:
        raise ValueError(
            ".env 파일에 TOSS_APP_KEY(또는 TOSS_CLIENT_ID)와 TOSS_APP_SECRET(또는 TOSS_CLIENT_SECRET)이 설정되지 않았습니다."
        )

    token_data = issue_token(client_id, client_secret)
    save_cached_token(token_data)
    print("✅ [발급 완료] 새 토큰이 정상적으로 발급되었으며 캐시에 저장되었습니다.")

    return token_data["access_token"]


if __name__ == "__main__":
    print("=" * 60)
    print("🚀 [1강 & 2강 실습] 토스증권 API 토큰 발급 테스트")
    print("=" * 60)

    try:
        token = get_access_token()
        # 보안을 위해 토큰의 앞뒤 일부만 마스킹하여 출력
        masked_token = token[:8] + "..." + token[-8:] if len(token) > 16 else token
        print(f"\n👉 현재 활성화된 토큰: {masked_token}")
        print("\n축하합니다! 토스증권 API 서버와 성공적으로 첫 통신을 마쳤습니다.")
    except Exception as e:
        print(f"\n❌ 오류 발생: {e}")

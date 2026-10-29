# 📝 토스증권 API & 파이썬 스터디 일지 (Study Log)

> **스터디 목표:** 토스증권 Open API를 활용한 파이썬 프로그래밍 기초 및 실전 자동화 구현  
> **저장소:** [github.com/realnihil/PythonStudy/tree/main/TossInvest_api_study](https://github.com/realnihil/PythonStudy/tree/main/TossInvest_api_study)  
> **현재 진도:** 2강 / 14회차 완료 (진도율: 14.3%)  
> **다음 세션 목표 (Next Up):** [3강 & 6강] 토스증권 REST API 구조 파악 및 주식 시세(현재가, 호가창) 조회 실습

---

## 📌 진도 현황 요약
- [x] **1강:** HTTP 통신 기초와 API 개념 (`requests`, REST API, JSON)
- [x] **2강:** 토스증권 API 키 발급 및 `.env` 보안 환경 설정 (토큰 발급 & 캐싱 구현)
- [ ] **3강 & 6강:** REST 엔드포인트 전체 지도 및 주식 시세 조회 (현재가, 호가, 캔들)
- [ ] **4강 & 5강:** 클래스(`class`) 기반 API 클라이언트 및 세션 자동화
- [ ] **7강:** 내 계좌 자산, 보유 종목 잔고, 주문 가능 예수금 조회
- [ ] **8강 & 9강:** 안전한 모의 주문(`dry-run`) 구조와 에러 백오프(429 Rate Limit 대응)
- [ ] **10강 & 11강:** `pandas` 데이터 처리, 이동평균선/RSI 지표 계산 및 종목 스크리너
- [ ] **12강:** SQLite 로컬 데이터베이스 시세 저장
- [ ] **13강 & 14강:** 스케줄러 자동 실행, 텔레그램 알림 및 실무 예외 처리

---

## 📅 세션별 상세 기록

### [세션 1] 2026-10-29: 스터디 환경 구축 & 첫 토큰 발급 성공
* **진행 강의:** 1강, 2강
* **주요 학습 내용:**
  1. **Git & 워크스페이스 구조화:**
     * `PythonStudy` 종합 저장소 내 `TossInvest_api_study` 독립 하위 폴더 구성
     * 연구소 PC와 집 PC 간의 원활한 동기화 환경 세팅
  2. **환경변수 보안 격리:**
     * `.env.example` 및 `.gitignore` 설정으로 실제 API Key(`.env`)의 GitHub 유출 원천 차단
  3. **환경 호환성 대책:**
     * `requirements.txt` 작성으로 어느 PC에서든 동일 패키지 원클릭 설치 가능
     * `from __future__ import annotations`를 적용하여 Python 3.9 ~ 3.13 전 버전 하위 호환성 확보
  4. **OAuth 2.0 인증 및 토큰 캐싱 메커니즘:**
     * API Secret Key를 매번 쏘지 않고 1일 유효 토큰(Bearer Token)을 발급받아 사용하는 원리 이해
     * 초당 호출 제한(Rate Limit) 방지를 위한 `.token_cache.json` 로컬 캐싱 구현
* **생성된 코드/파일:**
  * `lessons/01_auth_token/get_token.py` (토큰 발급 및 캐싱 스크립트)
  * `requirements.txt` (필수 패키지 목록)
  * `.gitignore`, `.env.example`, `README.md`
* **실행 결과 검증:**
  * 실제 토스증권 서버와 통신하여 `eyJraWQi...` 액세스 토큰 정상 발급 및 2회차 실행 시 캐시 재사용 확인 완료
* **다음 시간 계획:**
  * 발급받은 토큰을 헤더(`Authorization: Bearer <TOKEN>`)에 실어 토스증권 시세 조회 엔드포인트(`GET /api/v1/prices`, `GET /api/v1/orderbook`) 호출하기

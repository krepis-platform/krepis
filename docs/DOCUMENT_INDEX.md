# Krepis 로드맵 문서 구조 제안

## 📁 디렉토리 구조

```
docs/
├── vision/                          # 철학과 장기 비전
│   ├── KREPIS_MANIFESTO.md         # 전체 비전 (Why Krepis exists)
│   ├── SPEED_IS_INTELLIGENCE.md    # Micro-Swarm 철학
│   ├── ZERO_COST_RAZOR.md          # 기술 철학
│   └── NEURAL_OS_VISION.md         # Twin → Neural OS 진화 (Phase 5)
│
├── roadmap/                         # 실행 계획
│   ├── MASTER_ROADMAP.md           # 5단계 전체 조망 ⭐ 가장 중요
│   ├── phase1/                      # 백엔드 프레임워크
│   │   ├── OBJECTIVES.md
│   │   ├── TWIN_COMPLETION.md      # Twin 100% 완성 계획
│   │   └── BENCHMARKS.md           # 성공 기준
│   ├── phase2/                      # CLI 준자동화
│   │   ├── OBJECTIVES.md
│   │   ├── CLI_COMMANDS.md
│   │   └── TEMPLATE_SYSTEM.md
│   ├── phase3/                      # AI 도입
│   │   ├── OBJECTIVES.md
│   │   ├── SINGLE_AGENT.md         # 1개 AI로 시작
│   │   └── CODE_GENERATION.md
│   ├── phase4/                      # Twin 통합
│   │   ├── OBJECTIVES.md
│   │   ├── CI_CD_INTEGRATION.md
│   │   └── DIGITAL_TWIN.md
│   └── phase5/                      # AI 군단
│       ├── OBJECTIVES.md
│       ├── HYPER_SWARM.md          # 10K agents 아키텍처 ⭐
│       ├── GPU_OPTIMIZATION.md     # 5080 최적화 전략
│       └── MIGRATION_FROM_PHASE4.md
│
├── architecture/                    # 기술 설계
│   ├── framework/                   # Phase 1-2
│   │   ├── SOVEREIGN_KERNEL.md
│   │   ├── ZERO_COPY_FFI.md
│   │   └── MULTI_TENANT.md
│   ├── twin/                        # Phase 1, 4
│   │   ├── OVERVIEW.md              # 현재 Twin (Verification)
│   │   ├── TLA_SPECS.md
│   │   └── VERIFICATION_WORKFLOW.md
│   ├── ai-native/                   # Phase 3-5
│   │   ├── TRI_STORE.md            # Sled + SurrealDB + Qdrant ⭐
│   │   ├── SEMANTIC_METADATA.md    # AI를 위한 코드 프로토콜 ⭐
│   │   ├── SIGNATURE_LOADING.md    # Lazy loading 전략 ⭐
│   │   └── SHADOW_TAGGING.md       # 자동 메타데이터 생성 ⭐
│   └── neural-os/                   # Phase 5
│       ├── KERNEL_ARCHITECTURE.md  # Twin → Neural OS 전환
│       ├── V8_ISOLATES.md          # Agent 실행 환경 ⭐
│       ├── SHARED_MEMORY.md        # Zero-copy agent 통신 ⭐
│       └── GPU_SCHEDULER.md        # KV Cache Pinning 등 ⭐
│
├── implementation/                  # 구현 가이드
│   ├── phase1/
│   │   └── TWIN_INTEGRATION.md     # 현재 작업
│   ├── phase3/
│   │   ├── AI_SDK.md
│   │   └── CODE_ANALYSIS.md
│   └── phase5/
│       ├── AGENT_POOL.md
│       ├── DIFF_INFERENCE.md
│       └── MEMORY_LAYOUT.md
│
└── decisions/                       # ADR (Architecture Decision Records)
    ├── 001-why-twin-first.md        # Phase 순서 결정 근거
    ├── 002-sled-vs-postgres.md      # Index Store 기술 선택
    ├── 003-v8-vs-quickjs.md         # Agent 런타임 선택
    └── 004-tri-store-rationale.md   # 3개 DB 사용 이유
```

---

## 🎯 핵심 문서 Top 10 (우선순위 순)

### 1. `roadmap/MASTER_ROADMAP.md` ⭐⭐⭐ 최우선
**목적:** 전체 5단계를 한눈에 조망
**내용:**
- 현재 위치: Phase 1의 60%
- 각 Phase의 목표와 기간
- Phase 간 의존성
- 성공 기준 (KPI)
- 마일스톤 타임라인

**독자:** 투자자, 신규 팀원, 진혁님 본인 (6개월 후)

---

### 2. `roadmap/phase1/TWIN_COMPLETION.md` ⭐⭐⭐ 지금 당장 필요
**목적:** Twin 40% → 100% 완성 계획
**내용:**
- 남은 작업: ThreadStates, Dependencies, DPOR
- 각 작업의 TLA+ 스펙 참조
- 구현 순서와 테스트 전략
- 4주 완성 타임라인

**독자:** 진혁님 (실행 계획), AI Chief Architect (작업 지원)

---

### 3. `architecture/ai-native/TRI_STORE.md` ⭐⭐ Phase 5 핵심
**목적:** "확률이 아닌 확정" 아키텍처 상세 설계
**내용:**
- Tier 1 (Sled): O(1) 심볼 테이블
- Tier 2 (SurrealDB/Graph): O(1) 관계 추적
- Tier 3 (Qdrant): O(log N) 의미 검색
- 동기화 전략 (Two-Phase Commit)
- Phase별 구현 계획 (Phase 3부터 점진적)

**독자:** 아키텍트, 백엔드 개발자

---

### 4. `architecture/neural-os/V8_ISOLATES.md` ⭐⭐ Phase 5 핵심
**목적:** 10,000 AI agents 실행 환경
**내용:**
- V8 Isolate Pool 설계
- Agent lifecycle (spawn, execute, terminate)
- Rust FFI를 통한 Zero-copy 통신
- SharedArrayBuffer vs Rust memory
- Memory budget per agent

**독자:** 시스템 프로그래머, V8 전문가

---

### 5. `architecture/ai-native/SEMANTIC_METADATA.md` ⭐⭐ Phase 3-5
**목적:** AI를 위한 코드 프로토콜
**내용:**
- JSDoc 기반 semantic docstring
- YAML frontmatter for docs
- Hierarchical indexing
- Shadow tagging 메커니즘
- Template enforcement (USE)

**독자:** 프론트엔드/백엔드 개발자, AI 연구자

---

### 6. `architecture/neural-os/GPU_SCHEDULER.md` ⭐⭐ Phase 5 핵심
**목적:** 5080 GPU 최적화 전략
**내용:**
- KV Cache Pinning (시스템 프롬프트 고정)
- Diff-Only Inference (변경 부분만 GPU 전송)
- Batch scheduling (compatible prompts 묶기)
- Memory budget (16GB VRAM 관리)
- SchedulerOracle 활용 방안

**독자:** GPU 최적화 전문가, LLM 엔지니어

---

### 7. `roadmap/phase5/HYPER_SWARM.md` ⭐⭐ 최종 비전
**목적:** 10,000 AI agents 아키텍처 전체 그림
**내용:**
- Micro-Swarm 패턴 (작은 팀들의 협업)
- Agent 간 통신 (Memory pointer handoff)
- Context propagation (ctx 객체)
- Fault tolerance (agent crash 처리)
- Scaling strategy (1 → 10 → 100 → 10K)

**독자:** CTO, 시스템 아키텍트

---

### 8. `vision/SPEED_IS_INTELLIGENCE.md` ⭐ 철학
**목적:** 왜 "빠른 반복"이 "큰 모델"보다 나은가
**내용:**
- Local LLM의 초고속 추론
- 천재는 한 번에 완벽하지 않다 (iterate!)
- Phase 1-5가 이 철학을 어떻게 구현하는가
- Benchmark: Claude Opus vs 10K Local Llama3

**독자:** 비전에 공감할 사람들, 마케팅 자료

---

### 9. `architecture/ai-native/SIGNATURE_LOADING.md` ⭐ Phase 3-5
**목적:** Lazy loading으로 90% 토큰 절약
**내용:**
- Caller Mode: 시그니처만 (50 tokens)
- Implementer Mode: 전체 구현 (500 tokens)
- Graph pointer traversal
- 구현 예제 (TypeScript + Rust)

**독자:** AI 엔지니어, 컨텍스트 최적화 전문가

---

### 10. `roadmap/phase5/MIGRATION_FROM_PHASE4.md` ⭐ 전환 전략
**목적:** Phase 4 → Phase 5 전환을 안전하게
**내용:**
- Phase 4 완료 기준 (Twin 통합 검증)
- Tri-Store 도입 시점
- V8 Isolate Pool 구축 순서
- GPU 최적화 단계
- Rollback plan (Phase 5 실패 시)

**독자:** 프로젝트 매니저, 리드 개발자

---

## 📝 문서 작성 우선순위 (4주 계획)

### Week 1: 로드맵 기초
1. `roadmap/MASTER_ROADMAP.md` (전체 조망)
2. `roadmap/phase1/TWIN_COMPLETION.md` (현재 작업)
3. `decisions/001-why-twin-first.md` (왜 Phase 1부터?)

### Week 2: Phase 5 비전 (Master Report 기반)
4. `architecture/ai-native/TRI_STORE.md`
5. `architecture/neural-os/V8_ISOLATES.md`
6. `architecture/neural-os/GPU_SCHEDULER.md`

### Week 3: AI-Native 프로토콜
7. `architecture/ai-native/SEMANTIC_METADATA.md`
8. `architecture/ai-native/SIGNATURE_LOADING.md`
9. `architecture/ai-native/SHADOW_TAGGING.md`

### Week 4: 통합 및 전환
10. `roadmap/phase5/HYPER_SWARM.md`
11. `roadmap/phase5/MIGRATION_FROM_PHASE4.md`
12. `vision/SPEED_IS_INTELLIGENCE.md`

---

## 🎨 문서 템플릿 구조

각 문서는 다음 구조를 따름:

```markdown
# [문서 제목]

**Status:** [Draft | In Progress | Implemented | Archived]
**Phase:** [1 | 2 | 3 | 4 | 5]
**Last Updated:** YYYY-MM-DD

## TL;DR (1분 요약)
- 핵심 메시지 3줄

## Context (왜 이것이 필요한가?)
- 배경
- 해결할 문제

## Solution (어떻게 해결하는가?)
- 기술적 접근
- 아키텍처 다이어그램

## Implementation (어떻게 구현하는가?)
- 단계별 계획
- 코드 예제
- 테스트 전략

## Trade-offs (무엇을 희생하는가?)
- 장점
- 단점
- 대안들과 비교

## Success Criteria (어떻게 성공을 측정하는가?)
- 정량적 지표
- 정성적 목표

## Timeline (언제 실행하는가?)
- Phase 연계
- 의존성

## References
- TLA+ 스펙
- 논문
- 코드
```

---

## 🚀 즉시 시작 가능한 첫 문서

### `docs/roadmap/MASTER_ROADMAP.md` 초안

```markdown
# Krepis Master Roadmap: 5단계 진화 계획

**Status:** In Progress (Phase 1)
**Last Updated:** 2026-01-19

## 🎯 Ultimate Goal

**2027년 말까지:** RTX 5080 1대로 10,000개 AI agents를 운영하는 
**수학적으로 검증된 차세대 백엔드 프레임워크** 완성

## 📍 Current Position

**Phase 1 (60% 완료)**: 백엔드 프레임워크 + Twin 검증 도구

## 🗺️ 5단계 로드맵

### Phase 1: 차세대 백엔드 프레임워크 (Month 1-2) ✅ 진행 중

**목표:** Express보다 10배 빠르고 수학적으로 검증된 프레임워크

**핵심 작업:**
- ✅ VirtualClock (시간 관리)
- ✅ SimulatedMemory (메모리 일관성)
- 🚧 SchedulerOracle (이벤트 스케줄링)
- ⏳ ThreadStates (스레드 블록킹)
- ⏳ DPOR (효율적 상태 탐색)

**성공 기준:**
- [ ] Twin이 15,000,000+ 상태 검증
- [ ] Benchmark: Express 대비 10x throughput
- [ ] TLA+ 스펙 100% 대응

**Why This First?**
기초가 튼튼하지 않으면 그 위에 무엇을 쌓아도 무너진다.

---

### Phase 2: CLI 준자동화 (Month 3-4) ⏳ 대기 중

**목표:** Rails scaffold 수준의 개발 경험

**핵심 작업:**
- `krepis init` - 프로젝트 생성
- `krepis generate service UserService` - Boilerplate
- `krepis verify` - Twin 자동 검증
- `krepis benchmark` - 성능 측정

**성공 기준:**
- [ ] 5분 안에 CRUD API 생성
- [ ] 생성된 코드 Twin 검증 통과
- [ ] Template 라이브러리 10개 이상

**Why This Second?**
검증된 프레임워크를 쉽게 사용할 수 있어야 한다.

---

### Phase 3: AI 도입 (Month 5-6) ⏳ 대기 중

**목표:** GitHub Copilot보다 정확한 Krepis 특화 AI

**핵심 작업:**
- Single AI agent 통합
- Code generation (natural language → code)
- Twin 자동 검증 연동
- Semantic metadata 파싱 (JSDoc)

**성공 기준:**
- [ ] "로그인 기능 만들어줘" → 작동하는 코드
- [ ] AI 생성 코드 Twin 검증 통과율 95%+
- [ ] Hallucination 비율 < 5%

**Why This Third?**
프레임워크와 CLI가 안정된 후에 AI를 도입한다.

---

### Phase 4: Twin + 수학적 증명 통합 (Month 6-7) ⏳ 대기 중

**목표:** CI/CD 파이프라인에 형식 검증 통합

**핵심 작업:**
- GitHub Actions + Twin 통합
- Pull Request 자동 검증
- Production Digital Twin
- Realistic workload 시뮬레이션

**성공 기준:**
- [ ] PR에 "15M states verified" 배지
- [ ] Production 배포 전 Twin 시뮬레이션 필수
- [ ] Bug detection rate 증가 측정

**Why This Fourth?**
Twin이 개발 workflow의 핵심이 된다.

---

### Phase 5: AI 군단 운영 (Month 7-8) ⏳ 대기 중

**목표:** 5080 GPU에서 10,000 AI agents 실행

**핵심 작업:**
- Tri-Store (Sled + SurrealDB + Qdrant)
- V8 Isolate Pool (10K agents)
- GPU Optimization (KV Cache Pinning)
- Semantic Metadata Protocol
- Hyper-Swarm Architecture

**성공 기준:**
- [ ] 10,000 agents 동시 실행 (5080 16GB)
- [ ] Agent 간 통신 < 1ms (Zero-copy)
- [ ] GPU utilization > 90%
- [ ] Token efficiency: 90% 절약 (Lazy loading)

**Why This Last?**
Phase 1-4가 완성된 후에만 의미가 있다.

---

## 🔗 Phase 간 의존성

```
Phase 1 (Twin 100%) 
  ↓
Phase 2 (CLI + Templates)
  ↓
Phase 3 (Single AI agent)
  ↓
Phase 4 (Twin CI/CD 통합)
  ↓
Phase 5 (10K AI agents)
```

**각 Phase는 이전 Phase 완료 필수**

---

## 📊 Timeline Overview

```
2026 Jan  Feb  Mar  Apr  May  Jun  Jul  Aug  2027
  │ P1 │ P1 │ P2 │ P2 │ P3 │ P3 │ P4 │ P5 │
  └─────┴─────┴─────┴─────┴─────┴─────┴─────┘
   Twin  CLI   AI   Verify Swarm
```

**Total: 8 months**

---

## 🎓 핵심 교훈: Twin First

**왜 Twin을 먼저 완성하는가?**

1. **기초 = 검증**: 프레임워크의 안전성 증명
2. **차별화**: 다른 프레임워크가 못 하는 것
3. **신뢰**: "수학적으로 검증됨" 마케팅 가능
4. **Phase 2-5의 토대**: 모든 것이 Twin 위에 구축됨

**Twin 없이 AI 군단을 만들면?**
→ 모래 위의 성 🏰💥

---

## 📚 관련 문서

- Phase 1 상세: `roadmap/phase1/OBJECTIVES.md`
- Phase 5 비전: `roadmap/phase5/HYPER_SWARM.md`
- Tri-Store: `architecture/ai-native/TRI_STORE.md`
- 철학: `vision/SPEED_IS_INTELLIGENCE.md`
```
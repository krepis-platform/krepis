# Krepis Master Roadmap: 차세대 백엔드 프레임워크 5단계 진화

**Status:** Phase 1 In Progress (60%)  
**Version:** v1.0.0  
**Last Updated:** 2026-01-19  
**Owner:** Jinhyeok Lee  

---

## 🎯 Ultimate Vision

**2027년 말까지 달성할 목표:**

RTX 5080 GPU 1대로 **10,000개 AI agents**를 운영하면서,
**수학적으로 검증된** 차세대 백엔드 프레임워크를 완성한다.

---

## 📍 Current Position

```
Phase 1: 백엔드 프레임워크 구축  [████████████░░░░░░░░] 60%
  ├─ VirtualClock ✅ 완료
  ├─ SimulatedMemory ✅ 완료  
  ├─ SchedulerOracle 🚧 진행 중 (90%)
  ├─ ThreadStates ⏳ 대기 중
  ├─ Dependencies ⏳ 대기 중
  └─ DPOR Algorithm ⏳ 대기 중

Next: Twin 100% 완성 → Phase 2 CLI 개발
```

---

## 🗺️ 5단계 로드맵 Overview

### Timeline at a Glance

```
2026                                          2027
Jan  Feb  Mar  Apr  May  Jun  Jul  Aug  Sep
├────┼────┼────┼────┼────┼────┼────┼────┤
│ P1 │ P1 │ P2 │ P2 │ P3 │ P4 │ P5 │ P5 │
└────┴────┴────┴────┴────┴────┴────┴────┘
Twin   CLI   AI   Verify  Swarm

P1: 백엔드 프레임워크 + Twin (2개월)
P2: CLI 준자동화 (2개월)
P3: AI 단일 에이전트 (1개월)
P4: Twin CI/CD 통합 (1개월)
P5: AI 군단 운영 (2개월)
```

---

## Phase 1: 차세대 백엔드 프레임워크 (Month 1-2)

### 🎯 Phase Objective

**Express.js보다 10배 빠르고, 수학적으로 검증된 백엔드 프레임워크**

### 핵심 질문

- Krepis가 정말 Express보다 빠른가? → Benchmark 증명
- Krepis가 정말 안전한가? → Twin + TLA+ 증명

### Architecture

```
┌─────────────────────────────────────────┐
│     TypeScript Business Logic           │ ← 개발자가 작성
├─────────────────────────────────────────┤
│     Zero-Copy FFI                       │ ← 직렬화 없음
├─────────────────────────────────────────┤
│     Sovereign Kernel (Rust)             │ ← 고성능 런타임
│  ├─ HTTP Handler                        │
│  ├─ Memory Manager                      │
│  ├─ Multi-Tenant Isolator              │
│  └─ Event Scheduler                     │
└─────────────────────────────────────────┘
                  ↓
         Krepis Twin (검증)
  ┌──────────────────────────────┐
  │  VirtualClock                │ ← 시간 진행 검증
  │  SimulatedMemory             │ ← 메모리 일관성 검증
  │  SchedulerOracle             │ ← 스케줄링 공정성 검증
  └──────────────────────────────┘
                  ↓
          TLA+ Specifications
    (수학적 명세 = Ground Truth)
```

### 핵심 작업

**✅ 완료:**
- VirtualClock: 시간 진행과 이벤트 순서 관리
- SimulatedMemory: Relaxed memory model 시뮬레이션

**🚧 진행 중 (2주 완성 목표):**
- SchedulerOracle: Thread state 관리 및 event scheduling

**⏳ 대기 중 (4주 완성 목표):**
- ThreadStates: RUNNABLE → BLOCKED → COMPLETED 전환
- Dependencies: Task 간 의존성 및 deadlock detection  
- DPOR: Dynamic Partial Order Reduction (상태 공간 최적화)

### Success Criteria

**정량적:**
- [ ] Twin이 15,000,000+ 상태 검증 성공
- [ ] Benchmark: Express 대비 10x+ throughput
- [ ] TLA+ 스펙 100% 대응
- [ ] Kani formal verification 모든 proof 통과

**정성적:**
- [ ] "수학적으로 검증됨" 문구를 정당하게 사용 가능
- [ ] 개발자에게 "절대 race condition 없음" 보장 가능
- [ ] Realistic workload 시뮬레이션 결과 제시 가능

### Why This First?

**기초가 튼튼하지 않으면 그 위에 무엇을 쌓아도 무너진다.**

Phase 2-5의 모든 기능(CLI, AI, 군단)은 Phase 1 프레임워크 위에서 작동합니다.
프레임워크가 검증되지 않으면, 10,000개 AI가 있어도 소용없습니다.

---

## Phase 2: CLI 준자동화 (Month 3-4)

### 🎯 Phase Objective

**Rails scaffold 수준의 개발 경험 제공**

### 핵심 Commands

```bash
# 프로젝트 초기화
krepis init my-app

# 서비스 생성 (boilerplate)
krepis generate service UserService
krepis generate controller AuthController
krepis generate model User

# 검증 (Twin 자동 실행)
krepis verify
# → "15M states verified, 0 race conditions"

# 벤치마크
krepis benchmark
# → "10,543 req/sec (Express: 1,124 req/sec)"
```

### Architecture

```
┌─────────────────────────────────────────┐
│     Krepis CLI                          │
│  ├─ Template Engine                     │
│  ├─ Code Generator                      │
│  ├─ Twin Integration                    │
│  └─ Benchmark Suite                     │
└─────────────────────────────────────────┘
                  ↓
        Template Library
  ┌──────────────────────────────┐
  │  REST API                    │
  │  GraphQL                     │
  │  WebSocket                   │
  │  CRUD                        │
  │  Authentication              │
  └──────────────────────────────┘
```

### Success Criteria

- [ ] 5분 안에 완전한 CRUD API 생성
- [ ] 생성된 모든 코드 Twin 검증 100% 통과
- [ ] Template 라이브러리 10개 이상
- [ ] Documentation 자동 생성

### Why This Second?

**검증된 프레임워크를 쉽게 사용할 수 있어야 한다.**

Phase 1에서 프레임워크가 안전하다는 것을 증명했으니,
이제 개발자가 쉽게 사용할 수 있는 도구를 제공합니다.

---

## Phase 3: AI 도입 (Month 5)

### 🎯 Phase Objective

**GitHub Copilot보다 정확한 Krepis 특화 AI 코딩 도구**

### Architecture

```
    User Input (Natural Language)
              ↓
    ┌──────────────────────┐
    │   Single AI Agent    │
    │  (Local LLM)         │
    └──────────────────────┘
              ↓
    Code Generation (TypeScript)
              ↓
    ┌──────────────────────┐
    │   Twin Verification  │
    │  (자동 실행)          │
    └──────────────────────┘
              ↓
    검증 성공 → 코드 제공
    검증 실패 → AI 재생성
```

### Key Features

1. **Krepis Framework Awareness**
   - AI는 Krepis의 best practices를 이미 학습함
   - 생성 코드는 자동으로 프레임워크 규칙 준수

2. **Twin Integration**
   - AI가 생성한 코드 즉시 Twin 검증
   - 검증 실패 시 AI가 자동으로 수정

3. **Semantic Metadata Parsing**
   - JSDoc 주석으로 AI에게 힌트 제공
   - Shadow tagging으로 자동 메타데이터 생성

### Success Criteria

- [ ] "로그인 기능 만들어줘" → 작동하는 코드 생성
- [ ] AI 생성 코드 Twin 검증 통과율 95%+
- [ ] Hallucination rate < 5%
- [ ] 생성 속도 < 30초 (로컬 LLM)

### Why This Third?

**프레임워크와 CLI가 안정된 후에 AI를 도입한다.**

Phase 1-2가 없으면 AI가 무엇을 생성해야 할지 모릅니다.
검증 도구(Twin)가 없으면 AI 코드를 신뢰할 수 없습니다.

---

## Phase 4: Twin + CI/CD 통합 (Month 6)

### 🎯 Phase Objective

**GitHub PR에 "15M states verified" 배지 달기**

### Architecture

```
  Developer → git push → GitHub
                            ↓
                 GitHub Actions Trigger
                            ↓
              ┌──────────────────────┐
              │   Twin CI/CD Job     │
              │  1. Compile code     │
              │  2. Run Twin sim     │
              │  3. Generate report  │
              └──────────────────────┘
                            ↓
         Pull Request Comment
    ┌────────────────────────────────┐
    │ ✅ Verified: 15,234,567 states │
    │ ⏱️  Time: 3m 42s               │
    │ 🐛 Race conditions: 0          │
    │ 🔒 Deadlocks: 0                │
    └────────────────────────────────┘
```

### Key Features

1. **Automatic Verification**
   - 모든 PR에 Twin 자동 실행
   - 검증 실패 시 merge 차단

2. **Production Digital Twin**
   - 실제 서버 배포 전 Twin 시뮬레이션
   - Expected traffic pattern 테스트

3. **Performance Regression Detection**
   - Benchmark 자동 실행
   - 성능 저하 시 경고

### Success Criteria

- [ ] PR에 검증 배지 자동 표시
- [ ] Production 배포 전 Twin 시뮬레이션 필수
- [ ] Bug detection rate 측정 가능

### Why This Fourth?

**Twin이 개발 workflow의 핵심이 된다.**

Phase 1-3에서 Twin은 "도구"였지만,
Phase 4에서 Twin은 "필수 프로세스"가 됩니다.

---

## Phase 5: AI 군단 운영 (Month 7-8)

### 🎯 Phase Objective

**RTX 5080 GPU 1대에서 10,000 AI agents 동시 실행**

### Architecture: The Hyper-Swarm

```
┌─────────────────────────────────────────────────────┐
│               10,000 AI Agents                      │
│  ┌──────┐ ┌──────┐ ┌──────┐       ┌──────┐        │
│  │ V8   │ │ V8   │ │ V8   │  ...  │ V8   │        │
│  │ Iso  │ │ Iso  │ │ Iso  │       │ Iso  │        │
│  └──────┘ └──────┘ └──────┘       └──────┘        │
└─────────────────────────────────────────────────────┘
                      ↓
         Krepis Neural OS Kernel
┌─────────────────────────────────────────────────────┐
│  SimulatedMemory (Zero-Copy Agent Communication)    │
│  SchedulerOracle (GPU Time Allocation)              │
│  VirtualClock (Agent Synchronization)               │
└─────────────────────────────────────────────────────┘
                      ↓
              Tri-Store Knowledge Base
┌─────────────────────────────────────────────────────┐
│  Tier 1: Index Store (Sled) - O(1) symbol lookup   │
│  Tier 2: Graph Store (SurrealDB) - O(1) relations  │
│  Tier 3: Vector Store (Qdrant) - O(log N) semantic │
└─────────────────────────────────────────────────────┘
                      ↓
                RTX 5080 (16GB)
          KV Cache Pinning + Batching
```

### 핵심 기술

**1. Tri-Store Architecture**
- Tier 1 (Sled): O(1) 심볼 테이블
- Tier 2 (Graph): O(1) 의존성 추적  
- Tier 3 (Vector): O(log N) 의미 검색

**2. V8 Isolate Pool**
- 10,000 agents in separate V8 isolates
- Rust FFI를 통한 Zero-copy 통신
- Agent lifecycle: spawn → execute → terminate

**3. GPU Optimization**
- KV Cache Pinning (시스템 프롬프트 VRAM 고정)
- Diff-Only Inference (변경 부분만 GPU 전송)
- Batch scheduling (compatible prompts 묶기)

**4. Semantic Metadata Protocol**
- JSDoc semantic docstrings
- Shadow tagging (자동 메타데이터 생성)
- Lazy loading (Caller vs Implementer mode)

### Success Criteria

**정량적:**
- [ ] 10,000 agents 동시 실행 (5080 16GB VRAM)
- [ ] Agent 간 통신 latency < 1ms (Zero-copy)
- [ ] GPU utilization > 90%
- [ ] Token efficiency: 90% 절약 (Lazy loading)
- [ ] Tri-Store query < 10ms (p99)

**정성적:**
- [ ] "Speed is Intelligence" 철학 증명
- [ ] H100 없이 엔터프라이즈급 AI 작업 가능
- [ ] 다른 플랫폼이 따라올 수 없는 차별점

### Why This Last?

**Phase 1-4가 완성되어야만 Phase 5가 의미가 있다.**

- Phase 1 없으면: 프레임워크가 불안정 → AI 군단 무의미
- Phase 2 없으면: CLI 없음 → 개발자 사용 불가
- Phase 3 없으면: AI 경험 없음 → 군단 운영 불가능
- Phase 4 없으면: Twin 미통합 → 검증 불가

**모래 위의 성을 짓지 않는다.**

---

## 🔗 Phase 간 의존성

```
Phase 1 (Twin 100%)
  ↓ 필수: 프레임워크 검증 완료
Phase 2 (CLI + Templates)
  ↓ 필수: 개발 도구 안정화
Phase 3 (Single AI agent)
  ↓ 필수: AI 통합 경험
Phase 4 (Twin CI/CD)
  ↓ 필수: 검증 workflow 확립
Phase 5 (10K AI agents)
```

**각 Phase는 순차적으로 진행**
**이전 Phase가 100% 완료되어야 다음 Phase 시작**

---

## 🎓 핵심 교훈: Why Twin First?

### 1. 기초 = 검증

프레임워크가 안전한지 증명하지 못하면,
그 위에 무엇을 쌓든 신뢰할 수 없다.

### 2. 차별화 포인트

다른 백엔드 프레임워크는:
- "우리는 빠릅니다" (주장)

Krepis는:
- "우리는 수학적으로 검증됨" (증명)

### 3. 마케팅 가능

"TLA+ 명세 검증, 15M+ states 탐색"
→ 엔터프라이즈 고객에게 강력한 메시지

### 4. Phase 2-5의 토대

- CLI의 template → Twin 검증 통과 필수
- AI 생성 코드 → Twin 검증 통과 필수
- CI/CD → Twin 자동 실행
- AI 군단 → Twin이 Neural OS로 진화

**Twin 없이 AI 군단?**
→ 모래 위의 성 🏰💥

---

## 📊 Risk Assessment

### Phase 1 Risks

**Risk:** DPOR 구현 복잡도  
**Mitigation:** 논문 참조 구현 존재, 4주 버퍼

**Risk:** TLA+ 스펙 불완전  
**Mitigation:** 이미 15M+ states 검증 완료

### Phase 5 Risks

**Risk:** 10K agents = 메모리 폭발  
**Mitigation:** V8 Isolate는 경량 (각 ~1MB)

**Risk:** GPU OOM (Out of Memory)  
**Mitigation:** KV Cache Pinning + Diff inference

**Risk:** Tri-Store 동기화 복잡도  
**Mitigation:** Phase 3부터 점진적 도입 (1개씩)

---

## 📚 관련 문서

### Vision (철학)
- `vision/KREPIS_MANIFESTO.md` - 전체 비전
- `vision/SPEED_IS_INTELLIGENCE.md` - Micro-Swarm 철학
- `vision/ZERO_COST_RAZOR.md` - 기술 철학

### Roadmap (상세 계획)
- `roadmap/phase1/TWIN_COMPLETION.md` ⭐ 현재 작업
- `roadmap/phase5/HYPER_SWARM.md` ⭐ 최종 비전

### Architecture (기술 설계)
- `architecture/ai-native/TRI_STORE.md` ⭐ Phase 5 핵심
- `architecture/neural-os/V8_ISOLATES.md` ⭐ Agent 실행 환경
- `architecture/neural-os/GPU_SCHEDULER.md` ⭐ 5080 최적화

### Decisions (선택 근거)
- `decisions/001-why-twin-first.md` - Phase 순서 결정
- `decisions/002-sled-vs-postgres.md` - Index Store 선택

---

## 🚀 Next Actions

### This Week (2026-01-19 ~ 01-26)

**우선순위 1:** SchedulerOracle 통합 완료
- [ ] oracle.rs 구현 완성
- [ ] Simulator 통합
- [ ] Integration tests 작성

**우선순위 2:** ThreadStates 구현 시작
- [ ] TLA+ 스펙 리뷰
- [ ] Rust 타입 정의
- [ ] State transition logic

### Next 4 Weeks

**Week 2-3:** ThreadStates + Dependencies 완성  
**Week 4:** DPOR 알고리즘 구현  
**Week 5:** Twin 100% 완성 + 문서화

---

**"기초를 튼튼히, 한 걸음씩 확실하게"**

*This is not a sprint. This is a marathon with milestones.*
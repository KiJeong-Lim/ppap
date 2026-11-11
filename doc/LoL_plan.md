# LoL 개발 계획서

작성 2026-11-11 · 기준 커밋 `430f7a4` · 상태: 설계 결정 확정, M0 명세 승인, G0 통과(2026-11-11), M1 완료(2026-11-11 04:27). M1 다지기(엔진 최적화: P3, P4, 선언당 비용)를 함(2026-11-11 18:38, 14절). P5와 P6을 함(2026-11-11 19:43, 14절). 남은 최적화 작업을 표로 모으고 그중 O2·O5·O6을 함(2026-11-11 20:23, 14절). 다음은 M2

이 문서는 `codex.md`의 단기 계획 중 `LoL ALPHA1`, `Hol V2`, `LoL BETA`를 구체화한다.
2026-11-10의 ChatGPT 브리프는 폐기되었고, 이 문서는 그것을 전제하지 않는다.
"측정"이라고 쓴 수치는 이 문서를 쓰면서 직접 실행한 결과이고, "추정"·"목표"라고 쓴 수치는 그렇지 않다.

## 0. 요약

- **만드는 것**: 람다 프롤로그로 작성된 커널 위에서 돌아가는 증명 보조기. 이론은 Rocq의 pCIC의 부분 이론이다(우주 계층, 색인 있는 상호 귀납 가족, 의존 `match`, guard 검사를 거친 `fix`).
- **커널**: Hol 프로그램 `lol/hol/kernel.hol`이다. 선언은 이 프로그램이 hole 없는 항을 수락할 때만 환경에 들어간다. Haskell로 쓴 타입 검사기는 없다.
- **hole 채우기도 Hol이 한다**: 암시적 인자 추론은 Hol 프로그램 `lol/hol/elab.hol`이 커널의 환원·변환 clause를 hole이 있는 항에 그대로 써서 한다.
- **증명 모드는 Hol의 디버깅 모드다**: `elab.hol`은 단일화가 정하지 못한 `_`를 만나면 `debug`를 부른다. 거기서 `:assign`으로 그 자리의 항을 준다. tactic은 그 항을 정하는 규칙이고, `apply`는 새 `_`가 든 항을 넣는다.
- **Haskell은 호스트다**: 구문, 구동, 저장, 내보내기만 맡는다. 환원, 변환, 단일화, 타입 규칙은 Haskell에 구현하지 않는다.
- **믿을 근거**: 커널은 규칙과 1:1로 대응하는 약 1,500줄의 λProlog다. 모든 증명은 명시적 항으로 내보내져 Rocq가 다시 검사한다. 역설 모음과 변이 테스트가 각 검사가 실제로 건전성을 지탱함을 보인다.
- **버전**: `LoL ALPHA1`(tactic 없는 증명 스크립트 언어) → `Hol V2`(성능과 증명용 디버거) → `LoL BETA`(tactic, 대화형). `codex.md`의 순서 그대로다.
- **규모**: 약 4.8만 줄(추정), 작업 묶음 76개(10절).
- **엔진**: 커널이 Hol 위에서 도므로 Hol 일반 엔진의 성능이 곧 커널의 성능이다. 2026-11-11의 수정으로 메모리 회수와 호스트 서비스 비용이 해결되었다(2.5절).

## 1. 목표

끝났을 때 다음 문장들을 실행 가능한 증거와 함께 말할 수 있어야 한다.

| # | 주장 | 증거가 되는 완료 기준 |
|---|------|------------------------|
| H1 | 진짜 CIC다 | `doc/LoLCore.txt`의 모든 규칙에 번호가 있고 규칙마다 양성·음성 테스트가 있다. 우주 누적성, 색인·상호 귀납 가족, 의존 `match`, guard된 `fix`, 함수 η, (BETA부터) 우주 다형성 |
| H2 | 커널이 λProlog다 | `kernel.hol`의 모든 clause가 규칙 번호를 인용한다. 수락 경로에 Haskell로 쓴 환원·변환·타입 검사가 한 줄도 없다(스크립트가 검사) |
| H3 | 커널을 믿을 근거가 있다 | 라이브러리 전체의 Rocq export가 Rocq 9.0에서 컴파일된다. 변이 테스트 점수 90 % 이상. 건전성 검사마다 "그 clause를 지운 커널은 `False`의 증명을 수락한다"는 시연 |
| H4 | 증명 모드가 디버깅 모드다 | BETA의 `Proof. … Qed.`가 Hol 세션 하나이고, tactic은 Hol clause이며, 완성된 항은 같은 커널의 ground 실행으로 수락된다 |
| H5 | 실제로 수학을 한다 | 표준 라이브러리(ALPHA1 200개, BETA 800개 이상의 정의·정리)와 flagship 증명 3개 |
| H6 | 아래부터 위까지 자체 제작이다 | LGS → PGS → Hol(바이트코드 컴파일러 + C 실행기) → LoL. 외부 의존은 GHC, C 컴파일러, 검증용 Rocq뿐 |

## 2. 출발점: 지금 있는 것과 실측

### 2.1 자산

| 자산 | 위치 | LoL에서의 쓰임 |
|------|------|----------------|
| 렉서·파서 생성기 | `src/LGS`, `src/PGS` | LoL 렉서·파서를 `example/LoL/*.txt`에서 생성 |
| Hol BETA 프런트엔드 | `src/Hol/BETA` | fixity 후처리(`FixityResolver`), 표기(`Notation`), 진단(`Diagnostic`, `Z.Doc`), 모듈 로더의 설계를 재사용 |
| Hol V1 일반 엔진 | `src/Hol/V1`, `src/X` | 커널, elaborator, 증명 모드의 실행 |
| 세션 API | `Hol.V1.FullRuntime` | `withSession`, `nextSolution`, `takeSnapshot`/`restoreSnapshot`, `setWorkLimit`, `_PendingSubst`를 통한 할당 |
| 디버거 | `Hol.BETA.Runtime`, `Hol.BETA.Main` | sequent 꼴 상태 표시, `:assign`, `:show`, `debug` goal. 증명 모드의 본체 |
| Presburger 제약 저장소 | `src/Calc/Presburger`, `Hol.BETA.Arith` | 우주 레벨 제약(BETA) |
| 테스트 하네스 | `test/smoke.sh`, 사이드카 규약 | `.lol` + `.expected.txt` |
| Rocq 9.0.0 | 개발 기계 | 대조 오라클 |
| PnVRocqLib | 사용자의 Rocq 라이브러리(약 4.8만 줄) | 장기 이식 대상(13절) |

LoL 코드는 아직 한 줄도 없다.

### 2.2 probe 1: 커널

약 60줄짜리 검사기를 Hol로 써서 V1 일반 엔진(`V1 --test --general`)에서 돌렸다(부록 A).
범위는 `Prop`/`Type i`, 의존 곱, λ, 적용, δ 전개, 자연수와 그 recursor, 등식과 J, whnf 기반 변환 검사다. 항은 HOAS, 문맥은 `pi x\ of x A => …`로 표현했다.

- `forall n, add n 0 = n`의 귀납 증명과 `forall n, add 0 n = n`의 `refl` 증명을 수락한다.
- 틀린 증명, `Type 0 : Type 0`, `app zero zero`를 거부한다.
- 이 다섯 질의를 한 프로세스에서 로드부터 종료까지 0.05초에 처리한다(측정).

### 2.3 probe 2: hole을 Hol이 채운다

커널 위에 25줄을 얹어 암시적 인자를 추론했다(부록 A.3). `f_equal`에 해당하는 상수 `feq`의 인자 여섯 개 중 넷이 암시적이다.

```
?- pi k\ of k nat_ty => pi ih\ of ih (eq nat_ty (app (app add k) zero) k) =>
     elabc (rapp (rapp (rhd feq) (rtm sfn)) (rtm ih))
           (eq nat_ty (succ (app (app add k) zero)) (succ k)) (M k ih).

M := k\ app (app (app (app (app (app feq nat_ty) nat_ty) sfn) (app (app add k) zero)) k).
```

암시적 인자는 새 논리 변수로 두고, 명시적 인자를 왼쪽부터 검사하는 동안 Hol의 단일화가 그 변수를 채운다. 결과 타입과 기대 타입은 커널의 `whnf`로 양쪽을 줄여 가며 맞춘다. 채워진 항은 커널이 다시 수락한다. V1 일반 엔진과 BETA 모두 0.04초다(측정). goal 보류 같은 새 엔진 기능은 쓰지 않았다.

### 2.4 probe 3: 디버깅 모드에서 항 건설

그 elaborator에 규칙 두 개를 더했다(부록 A.4). `runder`는 raw 항의 `_`다.

```
elabc runder T M :- !, debug "goal", elabc R T M.
elabc (rlam F) T (lam A M) :- !, whnf T (prod A B), pi x\ of x A => elabc (F x) (B x) (M x).
```

`_`를 만나면 `debug`를 부르고, 그 자리에 올 raw 항 `R`을 사용자가 할당하면 그 항을 이어서 elaborate한다. 할당하는 항에 다시 `_`를 넣을 수 있다.
아래는 엔진을 고치지 않은 BETA 인터프리터에서의 세션이다(측정). 괄호 안은 대응하는 tactic이다.

```
?- elabc runder (prod nat_ty (n\ eq nat_ty (app (app add zero) n) n)) M.

*** debugger called with "goal"
[ ?- [ |- elabc R (prod nat_ty (n\ eq nat_ty (app (app add zero) n) n)) ?V_2233 ] ]
:assign ?V_2230 := rlam (n\ runder).                    (intro n)

*** debugger called with "goal"
[ ?- [ of x nat_ty |- elabc R (eq nat_ty (app (app add zero) x) x) (?V_2305 x) ] ]
    M := lam nat_ty ?V_2305
:assign ?V_2302 := rhd reflc.                           (apply eq_refl)

M := lam nat_ty (x\ app (app reflc nat_ty) (app (app add zero) x)).
```

`|-`의 왼쪽이 지역 문맥이고 오른쪽이 목표다. 지금까지 지어진 항은 치환으로 보인다. 둘째 단계에서 `reflc`의 암시적 인자 둘은 elaborator가 채웠다. 마지막 항을 커널에 따로 던지면 수락한다. V1 일반 엔진도 같은 자리에서 멈춘다.

같은 실험에서 드러난 빈 곳(측정):

| 관찰 | 뜻 |
|------|-----|
| 틀린 항을 할당하면 세션이 `no.`로 끝난다 | 실패한 단계가 증명 전체를 죽인다. 단계마다 snapshot을 찍고 실패하면 되돌린다 |
| 멈춘 뒤 계속하려면 `:d`로 디버깅을 끄고 진행해야 하고, 할당할 변수의 내부 이름(`?V_2302`)을 화면에서 읽어야 한다 | 세션 API가 멈춘 목표를 구조화해 넘기고 "다음 `debug`까지 계속"을 한 호출로 해야 한다 |
| 변수 판정을 이중 부정으로 써서 상태 표시에 `isvar … & !` 프레임이 섞인다 | `flex` 내장 술어가 필요하다 |
| `_`를 만나는 즉시 멈춘다 | 단일화가 정해 줄 `_`까지 묻게 된다. 적용 규칙의 순서를 "명시적 인자 → 결론 → 남은 `_`"로 둔다 |
| 커널의 `check`에 hole 규칙을 두고 논리 변수를 직접 할당하는 변형도 동작하지만, 할당하는 항에 새 변수를 둘 수 없다(`'?R' is not an active debugger variable`) | `_`를 raw 항의 상수로 두는 위 방식에는 이 문제가 없다. 그래서 위 방식을 택한다 |

### 2.5 측정: 엔진

프로세스 전체(로드, 타입 검사, 질의 컴파일 포함)를 `/usr/bin/time`으로 1회씩 쟀다. 메모리는 최대 RSS다.
가운데 열은 2026-11-11의 엔진 수정(호스트 정지 시 상태 전체를 내보내지 않음, clause 머리 우선 구체화, 압축 수집기) 뒤의 값이다. 수정 내용과 프로토콜은 `doc/HolV1.txt`의 "Host stops, clause exclusion and compaction" 절에 있다.

| 실험 | V1 일반 엔진 (`430f7a4`) | V1 일반 엔진 (수정 후) | BETA 인터프리터 |
|------|--------------------------|------------------------|------------------|
| `conv (mul 10 10) 100`, 단항 수, 순수 논리 | 0.11 s / 92 MB | 0.02 s / 22 MB | 7.75 s / 3.0 GB |
| `conv (mul 20 20) 400` | 0.58 s / 507 MB | 0.04 s / 26 MB | 124 s에서 중단 / 23 GB |
| `conv (mul 30 30) 900` | 2.96 s / 1.73 GB | 0.08 s / 26 MB | 실행하지 않음 |
| `conv (mul 100 100) 10000` | 실행하지 않음 | 0.65 s / 34 MB | 실행하지 않음 |
| `num 100` (산술 서비스 `>`, `is`를 100회 호출) | 0.57 s / 64 MB | 0.02 s / 20 MB | 0.03 s / 18 MB |
| `num 400` | 124 s에서 중단 / 2.5 GB | 0.02 s / 20 MB | 2.20 s / 43 MB |
| `num 10000` | 실행하지 않음 | 0.16 s / 34 MB | 실행하지 않음 |
| 깊이 400인 수를 순수 논리로 생성 | 0.02 s | 0.02 s | 0.03 s |

수정 후 변환 검사는 단계 수에 거의 비례한다(단항 ι 단계 하나에 약 65 µs). 2.2–2.4절의 probe는 수정 후 바이너리에서도 같은 답을 낸다.

### 2.6 여기서 나오는 결론

1. **커널을 Hol로 쓸 수 있다.** 의존 타입 검사기는 Hol V1로 지금 돈다.
2. **hole 채우기에 Haskell elaborator가 필요 없다.** 논리 변수가 메타변수이고 Hol의 단일화가 추론이다.
3. **디버깅 모드에서 항을 건설하는 설계는 지금 엔진에서 이미 동작한다.** 부족한 것은 2.4절 표의 것들이고 전부 좁고 구체적이다.
4. **엔진이 임계 경로다.** 커널이 Hol이므로 커널의 속도와 메모리는 일반 엔진의 것이다. 수정 전에는 ι 단계 900개짜리 변환 검사가 1.7 GB를 썼고, 수정 후에는 26 MB다. 남은 것은 단일화 비용(7.1절 P3)이다.
5. **호스트 서비스 경로는 고쳐졌다.** 호출 400회가 2분을 넘기던 것이 0.02초가 되었다. 그래도 커널은 서비스를 쓰지 않게 쓴다(레벨을 단항 항으로 표현). 서비스는 BETA의 레벨 제약에서 쓴다.

## 3. 설계 결정

**D1. 커널은 Hol 프로그램이다.** `lol/hol/kernel.hol`이 `doc/LoLCore.txt`의 규칙을 구현한다. 선언은 이 프로그램의 *ground 실행*(hole 없는 항, 논리 변수 없는 질의)이 성공할 때만 환경에 들어간다.
- 근거: 이 프로젝트의 목표가 "람다 프롤로그로 작성된 커널 위에서 돌아가는 증명 보조기"다. 2.2절이 가능함을 보였다.
- 대가: 커널의 속도와 메모리는 Hol 일반 엔진의 것이다(2.5절). 신뢰 기반에 Hol 엔진(프런트엔드, 컴파일러, C 실행기)이 들어간다.
- 독립 대조: Haskell로 두 번째 검사기를 쓰지 않는다. 모든 선언을 명시적 항으로 내보내 Rocq가 다시 검사한다(D2).
- 2026-11-11 초안은 신뢰 기반을 Haskell 커널에 두었다. 사용자가 방향을 바로잡았다.

**D2. LoL Core ⊆ Rocq pCIC.** LoL이 수락하는 선언은 (번역 후) Rocq도 수락해야 한다. LoL은 더 보수적일 수 있지만 더 관대해서는 안 된다.
- 결과: Prop에 대한 정의적 증명 무관성 없음, 레코드 η 없음, sub-singleton 제거 규칙은 Rocq와 동일, guard와 positivity는 Rocq보다 좁게.
- guard는 좁은 채로 두지 않는다. 이후 버전에서 Rocq와 같은 강도로 바꾼다(사용자 요구, 2026-11-11). `doc/LoLCore.txt` 7.4절에 약속과 최소 내용(검사 중 환원, `match` 결과와 중첩 `fix`로의 subterm 전달)을 적었다. 어느 버전에서 할지는 정하지 않았다.

**D3. 제거 형식은 `match` + `fix`.** (승인) recursor를 원시로 두지 않는다. recursor(`nat_rect` 등)는 `fix`와 `match`로 쓴 보통의 정의다. ALPHA1에서는 라이브러리가 필요한 것을 직접 정의하고, 자동 생성은 `induction` tactic과 함께 BETA에서 한다.
- Hol로의 구현: strict subterm 집합은 `=>`로 넣는 가정 `strict x`이고, "블록의 함수가 타입에 나타나지 않는다"는 scope 검사(`pi f\ T f = K`)다. 상호 `fix`는 `nat -> tm` 타입의 변수 하나를 묶어 표현한다.

**D4. 우주는 두 단계.** ALPHA1은 닫힌 레벨 `Type@{n}`과 누적성. BETA에서 선언 수준 우주 다형성과 레벨 추론.
- 커널에서 레벨은 단항 항(`lz`, `ls`)이고 비교는 순수 clause다. 호스트 서비스를 부르지 않는다.
- BETA의 레벨 추론은 레벨 hole을 `nat` 논리 변수로 두고 Hol의 Presburger 제약 저장소에 `=<` 제약으로 쌓는다.

**D5. 표면 문법은 Gallina의 항 문법을 따른다.** (승인) 다른 점(`Type@{n}`, 항으로 닫는 `Theorem … := t.`)은 `doc/LoLALPHA1.txt`에 모은다. 확장자는 `.lol`, 오브젝트는 `.lolo`.

**D6. hole 채우기는 Hol 프로그램 `elab.hol`이 한다.** (승인. 2026-11-11에 먼저 승인된 Haskell bootstrap 안을 같은 날 이 안으로 고쳐 다시 승인받았다)
- 승인된 D6은 ALPHA1에 Haskell bootstrap elaborator를 두는 것이었다. 그 근거는 "Hol elaborator는 goal 보류가 있어야 한다"였는데, 2.3절이 보류 없이 된다는 것을 보였다. 그리고 커널이 Hol이 되면 Haskell elaborator는 환원 규칙을 Haskell로 한 벌 더 가져야 한다. 그것이 "배보다 큰 배꼽"이다.
- 고친 내용: elaborator는 Hol 프로그램이고, 환원과 변환은 커널의 clause를 그대로 쓴다. 호스트는 표면 구문을 위치 표시가 달린 raw 항으로 옮기기만 한다.
- 범위는 승인된 표 그대로 고정한다.

  | `elab.hol`이 하는 것 | 하지 않는 것 |
  |---|---|
  | 암시적 인자 삽입, `_` | 레벨 추론, 우주 다형성(BETA) |
  | 1차 단일화와 패턴 단일화(커널의 `whnf`로 양쪽을 줄임) | 제약 보류, 백트래킹, 힌트 |
  | 단순한 `match`의 return 절 추론 | 중첩 패턴, 여러 scrutinee |
  | `{struct}` 추론(인자마다 guard 검사 시도) | `Section`, coercion, type class |

- `elab.hol`의 결과는 제안일 뿐이다. 수락은 커널의 ground 실행이 한다.
- 되돌릴 조건: M7에서 `elab.hol`이 씨앗 라이브러리를 예산 안에 처리하지 못하면, 승인된 대로 Haskell bootstrap으로 돌아간다.

**D7. 전역 환경은 Hol의 사실(fact)이다.** 수락된 선언마다 호스트가 `cst_type`, `cst_body`, 귀납 블록의 사실을 만든다. ALPHA1에서는 질의마다 그 선언이 의존하는 선언의 사실만 주입한다. Hol V2에서 지속 프로그램에 증분 추가한다.
- 전역 이름은 Hol 쪽에서 자연수 번호다(`cst 17`). 이름표는 호스트가 가진다.

**D8. 이론에 내장 상수는 없다.** `eq`, `nat`, `and`는 라이브러리의 귀납형이다.

**D9. 명세가 먼저다.** 규칙에는 번호(`[T-App]`, `[I-Pos]`, `[G-Match]`)가 있고 커널의 clause, 테스트, 오류 메시지가 그 번호를 인용한다. 진행은 달력이 아니라 게이트(11절)로 판정한다.

**D10. 증명 모드는 `elab.hol`을 디버깅 모드로 실행하는 것이다.** Hol의 디버깅 모드는 원래 이 용도로 설계되었다. 2.4절이 지금 엔진에서 된다는 것을 보였다.
- `Theorem t : T. Proof.`는 raw 항 `_`를 `T`에 대해 elaborate하는 세션을 연다.
- 단일화가 정하지 못한 `_`에서 `elab.hol`이 `debug`를 부른다. 그때 표시되는 sequent `[ 가정 |- elabc ?R T ?M ]`이 증명 상태다.
- tactic은 그 `?R`에 넣을 raw 항을 정하는 규칙이다. `exact t`는 `t`를, `intro x`는 `fun x => _`를, `apply f`는 `f _ … _`를 넣는다. 새 `_`는 elaboration이 거기 닿을 때 같은 규칙으로 다시 `debug`를 부른다. 새 목표를 위한 장치를 따로 두지 않는다.
- ALPHA1의 일괄 실행에서는 같은 자리가 "추론할 수 없음" 오류다. 증명 모드와 일괄 elaboration은 `_`에 대한 정책 하나만 다르다.
- 되돌리기는 단계마다 찍는 snapshot이다. 실패한 단계도 같은 snapshot으로 되돌린다(틀린 항을 넣으면 질의 전체가 실패하므로 snapshot 없이는 증명이 끝난다. 2.4절). 런타임이 관리하는 `:undo`는 두지 않는다는 기존 결정을 유지한다.
- `Qed`는 완성된 항을 커널의 ground 실행으로 수락시킨다. 그래서 `elab.hol`과 tactic은 신뢰 기반 밖이다.

**D11. 호스트는 의미를 구현하지 않는다.** Haskell 쪽(`src/LoL`)에는 환원, 변환, 단일화, 타입 규칙을 구현하지 않는다. 크기 예산(`doc/LoLALPHA1.txt` 0장)을 스크립트로 검사한다.

## 4. 구조

```
 .lol ─▶ 호스트(Haskell): 렉서·파서(LGS/PGS 생성), scope, fixity
           │ raw 항 (위치 표시, hole 자리 포함)
           ▼
   ┌─────────────────────────────────────────────────────────────┐
   │ Hol 엔진                                                     │
   │                                                             │
   │   elab.hol ──커널의 whnf/conv를 hole 있는 항에 사용──┐         │
   │      │ hole 없는 Core 항 (제안)                     │         │
   │      ▼                                             ▼         │
   │   kernel.hol   infer / check / conv / whnf                   │
   │                inductive / match / guard                     │
   │      ▲                                                       │
   │      │ BETA: elab.hol을 디버깅 모드로 실행, tactics.hol        │
   └──────┼──────────────────────────────────────────────────────┘
          │ ground 실행이 성공하면 수락
          ▼
        Env ─▶ .lolo ─▶ LoL --check-only (프런트와 elab 없이 커널만 다시 실행)
                 └────▶ Rocq export (.v) ─▶ rocq compile -noinit
```

세 가지 실행:

| 실행 | 내용 | hole의 처리 | 쓰임 |
|------|------|-------------|------|
| ground | hole 없는 선언을 `kernel.hol`로 검사 | 논리 변수가 있으면 거부 | 수락. 환경에 들어가는 유일한 길 |
| elaboration | `elab.hol`이 raw 항을 Core 항으로 옮기며 커널의 `whnf`·`conv`를 호출 | 풀리지 않은 `_`는 오류 | 암시적 인자 채우기(ALPHA1) |
| 대화형 | 같은 `elab.hol`을 디버깅 모드로 | 풀리지 않은 `_`에서 `debug` | 증명 모드(BETA) |

신뢰 기반: `kernel.hol`, Hol 엔진, 그리고 호스트 중 수락된 선언을 Hol 사실로 바꾸는 부분(`LoL.Hol.Embed`, `LoL.Env`).
신뢰 밖: 프런트엔드, `elab.hol`, 증명 모드와 tactic, 출력, export.

배치:

| 경로 | 내용 |
|------|------|
| `doc/LoLCore.txt` | Core 이론 명세(규범) |
| `doc/LoLALPHA1.txt`, `doc/LoLBETA.txt` | 버전별 계층·경계, 표면 언어, 명령, 파일 형식. 사용자가 검토하는 한국어판은 `_ko.txt`(`doc/LoLALPHA1_ko.txt`)이고 영문판과 함께 고친다 |
| `doc/HolV2.txt` | Hol V2 명세 |
| `doc/LoLBench.txt` | 측정 기록(방법, 수치, 수치가 보여 주지 않는 것) |
| `lol/hol/kernel.hol` | 커널 |
| `lol/hol/elab.hol` | hole 채우기 |
| `lol/hol/tactics.hol` | BETA: tactic(hole에 넣을 raw 항을 정하는 clause) |
| `lol/theories/` | 표준 라이브러리(`.lol`) |
| `src/LoL/Front/` | 생성된 `Lexer`·`Parser`, `Syntax`, `Scope`, `Fixity`, `Vernac` |
| `src/LoL/Core.hs`, `src/LoL/Hol/{Embed,Session}.hs`, `src/LoL/Env.hs` | Core 자료형(운반용), Core·raw ↔ Hol 항, 세션 구동, 선언 저장과 사실 생성 |
| `src/LoL/Export/Rocq.hs`, `src/LoL/Object.hs`, `src/LoL/Pretty.hs`, `src/LoL/Diagnostic.hs`, `src/LoL/Main.hs` | export, 오브젝트 파일, 출력, 진단, 디스패처 명령 `LoL` |
| `example/LoL/LoLLexer.txt`, `LoLParser.txt` | 생성기 입력 |
| `test/lol/` | `pos/`, `neg/`, `paradox/`, `mutants/`, `fuzz/`, `rocq.sh`, `budget.sh` |

저장소 규칙과의 관계: `ppap.cabal`은 에이전트가 편집하지 않으므로 작업 묶음마다 등록할 모듈 목록을 보고에 적는다. 그 전까지 테스트는 `test/v1/*.sh`처럼 `cabal exec -- ghc -isrc`로 직접 컴파일한다. `unsafe*`는 쓰지 않는다. 의존 패키지는 지금의 `build-depends`로 충분하도록 설계한다.

## 5. Core 이론 (요약)

규범은 `doc/LoLCore.txt`다. 여기서는 결정된 범위만 적는다.

### 5.1 문법

```
ℓ ::= n | u | ℓ+1 | max(ℓ, ℓ)                      레벨 (ALPHA1은 n만)
s ::= Prop | Type@{ℓ}
t ::= x | s | c@{ℓ̄} | I@{ℓ̄} | C@{ℓ̄}
    | forall x : t, t | fun x : t => t | let x := t : t in t | t t
    | match t as x in I _ ȳ return t with (C z̄ => t)* end
    | fix f_k { f_i (x̄ : t̄) {struct x_j} : t := t }*
```

### 5.2 sort, 곱, 누적성

```
[S-Prop]  Prop : Type@{1}
[S-Type]  Type@{ℓ} : Type@{ℓ+1}
[P-Prop]  A : s₁,  B : Prop        ⟹  forall x : A, B : Prop
[P-Type]  A : Prop,  B : Type@{ℓ}  ⟹  forall x : A, B : Type@{ℓ}
[P-Max]   A : Type@{ℓ₁},  B : Type@{ℓ₂}  ⟹  forall x : A, B : Type@{max(ℓ₁, ℓ₂)}
[C-Prop]  Prop ≤ Type@{ℓ}
[C-Type]  ℓ ≤ ℓ'  ⟹  Type@{ℓ} ≤ Type@{ℓ'}
[C-Pi]    A ≡ A',  B ≤ B'  ⟹  forall x : A, B ≤ forall x : A', B'
```

### 5.3 변환

β, δ(투명 상수), ζ, ι(`match`가 생성자를 만날 때, `fix`가 생성자로 시작하는 재귀 인자를 받을 때), 함수 η. 증명 무관성과 레코드 η는 없다(D2).

### 5.4 귀납 가족

지원: 상호 블록, 균일 매개변수, 색인, `Prop` 또는 `Type@{ℓ}`에 사는 가족.

- `[I-Pos]` strict positivity: 블록의 가족은 인자 타입의 결론 머리에만 나타난다.
- `[I-Univ]` `Type@{ℓ}`에 사는 가족의 생성자 인자 타입의 sort는 `Type@{ℓ}` 이하다.
- `[I-Elim-*]` `Prop`에 사는 가족은 `Prop`으로만 제거되고, 예외는 생성자가 없거나 하나이면서 인자가 전부 증명인 가족이다(`False`, `True`, `eq`, `and`, `Acc`).

ALPHA1에서 거부하는 것: nested 귀납형, 비균일 매개변수, 코귀납형.

### 5.5 `fix`와 guard

- `[G-App]` 본문에서 블록의 함수는 struct 인자 자리까지 적용된 꼴로만 나타나고, 그 인자는 strict subterm이다.
- `[G-Match]` subterm은 `match`로만 생긴다. scrutinee가 struct 인자이거나 strict subterm이면 가지의 재귀 인자는 strict subterm이다.
- `[G-Fun]` strict subterm을 인자에 적용한 것은 strict subterm이다.
- `[G-Type]` 블록의 함수는 바인더의 타입과 return 절에 나타나지 않는다.

guard는 쓰인 그대로의 항에 대해 검사하고 환원하지 않는다. Rocq보다 좁다. 이후 버전에서 Rocq와 같은 강도로 바꾼다(`doc/LoLCore.txt` 7.4절).

### 5.6 Rocq와 맞춰 본 것

`doc/LoLCore.txt` 10.2절의 열두 사례(sort, 곱, 누적성, positivity, 우주 제약, 제거 제한, guard)를 Rocq 9.0.0의 `rocq compile -noinit`로 확인했다. 수락·거부가 전부 규칙과 같고, 거부 사유도 해당 규칙에 대응하는 Rocq의 오류다.

## 6. 표면 언어

| 기능 | ALPHA1 (M2–M6) | ALPHA1 (M7 이후) | BETA |
|------|----------------|------------------|------|
| 명시적 항, `Inductive`, `Fixpoint`, `Definition`, `Theorem … := t`, `Axiom` | ✔ | ✔ | ✔ |
| `Check`, `Compute`, `Print`, `Print Assumptions`, 파일 모듈과 `Import` | ✔ | ✔ | ✔ |
| 암시적 인자 `{A : T}`, `_`, `Arguments`, `Infix`·`Notation`(연산자), 숫자 리터럴 | | ✔ | ✔ |
| `match`의 return 절 생략(단순한 경우), `{struct}` 생략 | | ✔ | ✔ |
| `Proof. … Qed.`, tactic, 대화형 단계 실행 | | | ✔ |
| 레벨 없는 `Type`, 우주 다형 선언 | | | ✔ |

M5 시점(명시적):

```coq
Inductive nat : Type@{0} :=
| O : nat
| S : nat -> nat.

Inductive eq (A : Type@{0}) (x : A) : A -> Prop :=
| eq_refl : eq A x x.

Fixpoint add (n m : nat) {struct n} : nat :=
  match n return nat with
  | O => m
  | S p => S (add p m)
  end.

Definition f_equal (A B : Type@{0}) (f : A -> B) (x y : A) (e : eq A x y) : eq B (f x) (f y) :=
  match e in eq _ _ z return eq B (f x) (f z) with
  | eq_refl _ _ => eq_refl B (f x)
  end.

Theorem add_n_O : forall n : nat, eq nat (add n O) n :=
  fix F (n : nat) {struct n} : eq nat (add n O) n :=
    match n as k return eq nat (add k O) k with
    | O => eq_refl nat O
    | S p => f_equal nat nat S (add p O) p (F p)
    end.
```

M7 이후(`elab.hol`):

```coq
Infix "+" := add (at level 50, left associativity).
Infix "=" := eq (at level 70, no associativity).

Theorem add_n_O : forall n : nat, n + O = n :=
  fix F (n : nat) : n + O = n :=
    match n with
    | O => eq_refl
    | S p => f_equal S (F p)
    end.
```

BETA:

```coq
Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n as [| n IH]; intros m.
  - rewrite add_n_O. reflexivity.
  - simpl. rewrite IH. rewrite add_n_Sm. reflexivity.
Qed.
```

세 예제는 Rocq 9.0.0으로 확인했다. 첫째는 아래 export 규칙으로 옮긴 뒤 `rocq compile -noinit`를 통과하고, 둘째의 항과 셋째의 스크립트는 Rocq의 표준 prelude에서 그대로 통과한다(`add_n_Sm`은 `n + S m = S (n + m)` 방향의 보조정리).

export 규칙(M3):

- `Type@{0}`은 `Set`으로, `Type@{n}`(n ≥ 1)은 `Universe L1 L2 …`와 `Constraint Set < L1.`, `Constraint L1 < L2.`로 선언한 전역 우주로 옮긴다.
- `A -> B`는 `forall _ : A, B`로 출력한다. `-noinit`에서는 `->` 표기가 정의되어 있지 않다(확인함).
- `Theorem name : T := t.`는 `Definition`으로 출력한다.
- 귀납형마다 Rocq가 `I_rect` 등을 자동 생성하므로 같은 이름의 LoL 정의는 export에서 이름을 바꾼다.

## 7. Hol 쪽에 필요한 것

"Hol V1의 성능을 더 개선해야 하는가"의 답은 "그렇다, 일반 엔진의 복잡도부터"다.
LoL의 프로그램은 HOAS, `pi`, `=>`를 쓰므로 항상 일반 엔진(version 2)에서 돈다. Einstein에서 Teyjus를 이긴 1차 전용 경로는 LoL과 무관하다.

### 7.1 성능 불변식

| # | 불변식 | 지금 (측정) | 필요한 시점 |
|---|--------|-------------|-------------|
| P1 | 호스트 서비스 한 번의 비용은 그 요청의 인자 크기에 비례한다 | 수정 후 `num 10000`이 0.16초. 산술이 없는 `=`와 전제를 줄 수 없는 `=>`는 호스트로 나가지 않는다(2026-11-11 17:59). 남은 것: 호스트가 제약이나 산술 전제를 들고 있는 프로그램은 정지마다 상태 전체를 내보낸다. 내보낸 변수의 식별자는 해제되지 않는다 | BETA(레벨 제약). 커널은 서비스를 쓰지 않고, 호스트 정지도 없다 |
| P2 | 결정적 실행의 메모리는 살아 있는 자료에 비례한다 | 수정 후 `mul 100 100` 변환에 34 MB | ALPHA1 |
| P3 | head 단일화의 비용은 패턴 크기에 비례한다(이미 정규형인 부분항을 복사하거나 다시 정규화하지 않는다) | 변수가 없는 항(안정한 항)에 대해서는 됨(2026-11-11 17:59, 14절): nominal과 λ가 있어도 방문하거나 복사하지 않는다. 변수가 남은 항은 여전히 그 부분을 다시 짓는다 | ALPHA1 |
| P4 | 항의 깊이에 고정 한계가 없다 | 됨(2026-11-11 18:35, 14절): 깊이 10⁵의 정규형 2.31초. 남아 있던 한계 8192(wire import, export의 함수 쪽, 단일화의 마지막이 아닌 인자)도 없앴다(2026-11-11 20:23) | ALPHA1 |
| P5 | 프로그램은 한 번 컴파일하고 질의와 새 사실만 증분 컴파일한다 | 호스트에 대해서는 됨(2026-11-11 19:43, 14절): 기계가 프로그램을 유지하고 사실과 질의를 조각으로 받는다. 선언당 0.15 ms이고 앞선 선언의 수와 무관하다. 남은 것: 기계가 든 환경이 아닌 환경을 물으면 그 환경을 다시 싣는다. REPL(`V1 --test`)은 여전히 질의마다 모듈 전체를 컴파일한다 | ALPHA1(호스트). REPL은 Hol V2 |
| P6 | 사실의 조회는 첫 인자로 색인된다 | 됨(2026-11-11 19:43, 14절): 술어와 첫 인자(자연수 리터럴, 보통 상수가 머리인 항)로 색인한다. 지역 가정은 선형 탐색 그대로다 | ALPHA1 |

목표:

| 벤치마크 | 목표 | 시점 |
|----------|------|------|
| B1 `conv (mul 100 100) 10000` | 0.5초 이내, 100 MB 이내(수정 후 0.65초, 34 MB. 2026-11-11 18:38 기준 0.39초, 28 MB: 충족) | ALPHA1 |
| B2 씨앗 라이브러리 전체의 ground 검사 | 120초 이내, 1 GB 이내 | ALPHA1 |
| B3 깊이 10⁵ 항의 단일화와 출력 | 성공(2026-11-11 18:35: 깊이 99856의 정규형을 짓는 데 2.31초, 깊이 16384의 정규형을 호스트까지 내보내 비교하는 테스트 통과) | ALPHA1 |
| B4 `num 10000` | 1초 이내(수정 후 0.16초) | Hol V2 |
| B5 Einstein, 일반 엔진 강제 | Teyjus의 10배 이내(수정 전 약 146배. 수정 후 일반 엔진은 1.72초에서 0.37초가 되었으나 Teyjus와 다시 비교하지는 않았다) | Hol V2 |

P1과 P2의 수정은 2026-11-11에 했고 `doc/HolV1.txt`에 기록했다. 기존 smoke 164개는 수정 뒤에도 전부 통과한다.

### 7.2 기능

| # | 기능 | 필요한 이유 | 시점 |
|---|------|-------------|------|
| F1 | `flex X` 내장 술어 | `elab.hol`과 커널의 `flex` clause | 완료(2026-11-11). 명세는 `doc/HolBETA.txt` 3.6절 |
| F2 | 멈춘 세션의 목표를 구조화해 호스트에 넘기는 API(가정, 명목 상수, goal 항, 할당할 변수) | 증명 상태 표시, tactic의 입력 | Hol V2 |
| F3 | "다음 `debug`까지 계속"과 단계별 snapshot을 묶은 세션 호출 | 2.4절의 표 | Hol V2 |
| F4 | 지속 프로그램과 사실의 증분 추가(P5, P6) | 선언마다 커널을 다시 컴파일하지 않기 위해 | 엔진과 호스트는 됨(2026-11-11 19:43, `Full.Engine`). REPL은 Hol V2 |
| F5 | `main` 진입점과 독립 실행(elpi식) | `codex.md`의 Hol V2 항목 | Hol V2 |

초안에 있던 "mode 선언과 goal 보류", "`:assign`의 새 변수"는 필수 목록에서 뺐다. 2.3절과 2.4절이 그것 없이 된다는 것을 보였다. 필요해지는 경우(보류해야만 풀리는 제약)가 실제로 나오면 그때 명세한다.

### 7.3 커널이 쓰는 Hol의 범위

커널은 Hol의 좁은 부분만 쓴다. 엔진의 버그가 커널의 버그가 되는 면적을 줄이기 위해서다.

- 산술, Presburger, `print` 외의 I/O, `sigma`, `;`를 쓰지 않는다(`print`는 거부 사유 보고에만).
- cut은 "이 clause를 골랐다"는 뜻으로만 쓴다(패턴이 맞은 직후).
- 지역 변수는 `pi`로, 그 타입은 `=>`로 넣는 가정으로 다룬다.
- `flex`로 시작하는 clause는 ground 실행에서 실행되지 않는다. 그 clause들은 `elab.hol`이 hole 있는 항에 커널의 `whnf`·`conv`를 쓸 때 엔진이 후보를 생성하지 않게 한다.
- 커널은 `debug`를 부르지 않는다. `debug`는 `elab.hol`의 것이다.

## 8. 마일스톤

완료 기준은 모두 명령 하나로 재현되는 검사다. WP는 사용자가 한 번에 검토할 수 있는 변경 묶음(코드 약 1,500줄 이하, 테스트, 명세 반영)이다.

### 8.1 의존 관계

```
M0 ─▶ M1 ─▶ M2 ─▶ M3 ─▶ M4 ─▶ M5 ─▶ M6 ─▶ M7 ─▶ M8 ═▶ ALPHA1
H1 ─────────────────────▲                              (H1은 M1과 동시에 시작)
H2 ──────────────────────────────────▲                 (flex 내장은 M7 전에)
H3 ─▶ H4 ─▶ H5, H6 ═▶ Hol V2
ALPHA1 + Hol V2 ─▶ T1 ─▶ T2 ─▶ T3 ─▶ T4, T5 ═▶ BETA    K5, L2, L3는 T2 뒤
```

### 8.2 LoL ALPHA1: tactic 없는 CIC 증명 스크립트 언어

| M | 내용 | 산출물 | 완료 기준 | WP |
|---|------|--------|-----------|----|
| M0 | 명세 고정 | `doc/LoLCore.txt`, `doc/LoLALPHA1.txt`, 테스트 규약 | 모든 규칙에 번호. 계층과 경계. Rocq와의 차이 표. 사용자 승인 | 2 |
| M1 | 커널 I: PTS 핵심 | `kernel.hol`(sort, 곱, λ, let, 적용, δ, 변환과 η, 누적성), `LoL.Core`, `LoL.Hol.{Embed,Session}`, `LoL.Env` | 다형 항등·합성·Church 수·Leibniz 등식 수락. `Type@{n} : Type@{n}` 거부. Hurkens 항은 거부되고 해당 clause를 바꾼 변이 커널에서는 수락. 논리 변수나 잔여 제약이 남은 답은 수락으로 치지 않음을 테스트. Core ↔ Hol 항 왕복 성질 테스트 | 4 |
| M2 | 표면 I: 구문과 명시적 번역 | 생성기 입력, `Front/*`, `Pretty`, `Diagnostic`, 디스패처 명령 `LoL` | 사이드카 테스트. 출력 → 재파싱 → α-동치 왕복. 위치 있는 GHC식 진단 | 4 |
| M3 | Rocq 대조 I | `Export/Rocq.hs`, `test/lol/rocq.sh`, PTS 항 생성기 | 양성 테스트 전부가 `rocq compile -noinit` 통과. `Compute` 결과 일치. 생성 사례 10⁴개에서 "LoL 수락, Rocq 거부" 0건 | 2 |
| M4 | 커널 II: 귀납 가족과 `match` | `kernel.hol`의 귀납 선언 검사(positivity, 우주, 제거 sort), `match` 타이핑, ι. 표면의 `Inductive`·`match` | `nat`, `bool`, `list`, `eq`, `and`, `or`, `ex`, `False`, `True`, `Acc`, `vec`, `fin`, `even`/`odd` 수락. 음성 사례 30개 이상이 지정된 규칙 번호로 거부. positivity clause를 지운 변이에서 `False` 도출 | 4 |
| M5 | 커널 III: `fix`와 guard | `kernel.hol`의 `fix` 타이핑과 guard. 표면의 `Fixpoint`·`fix` | `add`, `mul`, `app`, `rev`, `map`, `vappend`, 상호 재귀, `Acc` 재귀 수락. guard 음성 20개 이상 거부. guard clause를 지운 변이에서 `False` 도출. 재귀 정의 생성기로 Rocq 대조, 위반 0건 | 3 |
| M6 | 환경, 오브젝트, 재검사 | 불투명 상수와 공리 추적, `Object.hs`(`.lolo`), `LoL --check-only`, 모듈과 `Import` | 변조한 `.lolo` 거부. 재검사 판정이 원 판정과 동일. 순환·중복 import 진단 | 3 |
| M7 | hole 채우기 | `elab.hol`, raw 항 인코딩, 암시적 인자·`Arguments`·`Infix`·숫자 리터럴 | D6의 표 왼쪽 열 전부에 테스트. 풀리지 않은 hole은 위치와 함께 보고. `elab.hol`의 결과가 전부 ground 실행을 통과. 작업량 제한으로 무한 생성이 오류로 끝남을 테스트 | 4 |
| M8 | 씨앗 라이브러리와 굳히기 | `lol/theories/{Logic,Nat,Bool,List,Vec,Wf}.lol`, 변이 모음, 거부 사유 보고, 예산 스크립트 | 정의·정리 200개 이상이 ground 검사, `--check-only`, Rocq export를 통과. B1–B3. 변이 40개 이상에서 점수 90 % 이상. 오류 메시지 골든 테스트 50개 이상. `test/lol/budget.sh` 통과 | 5 |

### 8.3 Hol V2

| H | 내용 | 완료 기준 | WP |
|---|------|-----------|----|
| H1 | 성능 불변식 P1–P4 | 작업량 카운터 기반 회귀 테스트. 기존 smoke 전체 통과 | 3 |
| H2 | F1 | `flex`의 명세와 테스트. BETA와 V1의 판정 일치. 2.4절의 세션에서 `isvar` 프레임이 사라짐 (2026-11-11 완료. 마지막 항목은 `elab.hol`이 생기는 M7에서 확인한다) | 2 |
| H3 | F2, F3 | 2.4절의 세션을 API만으로 재현: 목표와 문맥을 구조로 받고, raw 항을 할당하고, 다음 `debug`까지 진행하고, 실패한 단계를 되돌린다 | 3 |
| H4 | F4(P5, P6) | 선언 1000개 연속 처리 시간이 선형 (2026-11-11 19:43 완료: 51200개까지 선언당 0.15 ms) | 2 |
| H5 | F5 | 독립 실행 진입점과 사용 예 | 1 |
| H6 | 벤치마크 | B4, B5 측정과 기록. 고차 벤치마크 모음의 Teyjus 대비 표 | 2 |

### 8.4 LoL BETA: tactic과 대화형 실행기

| 항목 | 내용 | 완료 기준 | WP |
|------|------|-----------|----|
| T1 | 증명 모드 핵심 | `Theorem … . Proof.`가 `_`를 elaborate하는 세션을 연다. `Show`, `refine t`, `exact t`, `Undo`, `Abort`, `Qed` | 실패한 단계는 직전 snapshot으로 돌아가고 사유를 보고한다. `Qed`는 ground 실행. 2.4절의 세션이 LoL 구문으로 재현됨 | 3 |
| T2 | 기본 tactic | `intro(s)`, `apply`, `assumption`, `reflexivity`, `symmetry`, `transitivity`, `exists`, `split`, `left`, `right`, `constructor`, `exfalso`, `destruct`, `induction`, `rewrite`, `unfold`, `simpl`, `change`, `discriminate`, `injection`, `assert`, `specialize`. 전부 "`_` 자리에 넣을 raw 항을 정하는 Hol clause"다 | tactic마다 양성·음성 테스트. tactic이 만든 항은 전부 ground 실행 통과 | 6 |
| T3 | tactical | `;`, `try`, `repeat`, `first`, bullet, `all:` | 실패 시 상태 불변 | 2 |
| T4 | 사용자 정의 tactic | 사용자가 Hol 파일로 tactic을 추가 | 라이브러리의 tactic 일부를 사용자 수준 파일로 재정의 | 2 |
| T5 | 스크립트 실행기 | 문장 단위 전진·후퇴, 목표 표시 | 스크립트 재생이 일괄 실행과 같은 판정 | 3 |
| K5 | 우주 다형성과 레벨 추론 | `kernel.hol`의 레벨 식과 다형 선언, 레벨 hole을 Presburger 제약으로 | 레벨 없는 `Type`으로 쓴 라이브러리가 수락됨. 다형 `list`, `prod`, `eq`. Rocq export 방식을 정하고 대조에 포함 | 4 |
| L2 | 표준 라이브러리 확장 | 순서 관계, 나눗셈과 gcd(well-founded 재귀), `Permutation`, `Forall`, 결정 가능성, `option`/`sum`/`prod`/`sig` | 정의·정리 800개 이상 | 6 |
| L3 | flagship | (1) 삽입 정렬과 병합 정렬의 검증, (2) 소수의 무한성, (3) STLC의 progress와 preservation | 커널과 Rocq export 통과 | 6 |

T2에서 정할 것: `_`를 묻는 순서. 2.4절의 규칙은 `_`를 만나는 즉시 멈춘다. `apply f`가 넣는 `f _ … _`에서는 결론을 목표와 먼저 맞춰야 맞지 않는 보조정리에서 바로 실패하고, 단일화가 정해 주는 인자를 사용자에게 묻지 않는다. 그래서 `elab.hol`의 적용 규칙을 "명시적으로 쓴 인자 → 결론 비교 → 아직 정해지지 않은 `_`" 순서로 둔다. 순서는 `elab.hol`의 일이고 커널의 건전성과 무관하다.

### 8.5 그 뒤 (전망)

하기로 정해진 것: guard 조건을 Rocq와 같은 강도로 바꾸기(`doc/LoLCore.txt` 7.4절). 변이·역설 모음과 Rocq 대조("LoL 수락 ⟹ Rocq 수락"에 더해 guard에 한해서는 그 역도)를 같이 넓힌다.

전망: 중첩 패턴 컴파일, `Section`, type class, coercion, LSP 서버, nested 귀납형, Rocq의 fully explicit 출력을 읽는 importer, PnVRocqLib의 한 조각 이식.

## 9. 검증 전략

1. **규칙 단위 테스트.** 규칙 번호마다 그 규칙으로 수락되는 최소 사례와 그 규칙 위반으로 거부되는 최소 사례. 음성 테스트는 거부 여부가 아니라 보고된 규칙 번호를 확인한다.
2. **역설 모음(`test/lol/paradox/`).** 건전성 검사마다 "그 검사가 없으면 `False`가 증명되는 항"을 둔다: 우주 검사(Hurkens), positivity, guard, `[I-Univ]`, `[I-Elim-Prop]`. 정상 커널은 거부하고 그 clause만 지운 변이 커널은 수락함을 보인다.
3. **변이 테스트(`test/lol/mutants/`).** `kernel.hol`에 버그를 하나씩 심은 패치 40개 이상(clause 삭제, 전제 삭제, 레벨 비교 뒤집기, 치환 자리 바꾸기 등). 테스트 모음이 죽인 변이의 비율이 점수다.
4. **Rocq 대조.** 양성 코퍼스 전체를 export해 컴파일한다. 생성기로 만든 사례에서 불변식 "LoL 수락 ⟹ Rocq 수락"을 검사한다. LoL만 거부한 사례는 보수성 보고서로 모은다. `Compute`의 정규형도 대조한다.
5. **ground 판정의 엄격함.** 답에 논리 변수나 잔여 제약이 남으면 수락이 아니다. 작업량 제한에 걸린 실행은 거부도 수락도 아닌 오류다. 둘 다 테스트한다.
6. **엔진 쪽 증거.** 커널이 쓰는 Hol의 범위(7.3절)에 대한 엔진 테스트: HOPU의 scope 검사, cut, `=>`의 순서. 기존 smoke와 BETA·V1 대조가 여기 들어간다.
7. **재현.** `.lolo` 재검사, 측정 기록의 프로토콜 명시.

Rocq 대조가 보여 주지 않는 것: Rocq 자신의 버그, LoL이 Rocq보다 좁은 부분의 완전성.

운영 규칙: 벤치마크와 fuzz는 항상 시간 제한과 메모리 상한을 걸고 실행한다. 2.5절의 측정 중 BETA 실행 하나가 23 GB를 써서 WSL2가 종료되었다.

## 10. 규모와 순서

코드 규모(추정):

| 구성 요소 | 줄 수 |
|-----------|-------|
| `kernel.hol` | 1,500 |
| `elab.hol` | 800 |
| `tactics.hol`과 증명 모드의 Hol 쪽 | 2,500 |
| 호스트(Haskell): 프런트, 구동, 환경, 출력, 진단, export, 오브젝트 | 6,000 |
| 증명 모드의 호스트 쪽(세션, 목표 표시, 스크립트 실행기) | 2,000 |
| Hol V2(C와 Haskell) | 4,000 |
| 테스트, 생성기, 변이 | 8,000 |
| 라이브러리(`.lol`) | 18,000 |
| 명세와 기록 | 5,000 |
| 합계 | 약 47,800 |

작업 묶음:

| 버전 | WP | 기간(추정, WP당 검토 포함 1–3일 가정) |
|------|----|----------------------------------------|
| LoL ALPHA1 | 31 | 6–19주 |
| Hol V2 | 13 | 3–8주, ALPHA1과 병행 |
| LoL BETA | 32 | 6–19주 |

기간은 WP 수에 가정(WP당 1–3일, 주 5일)을 곱한 값일 뿐이다. M1이 끝나면 실제 WP당 소요로 다시 계산한다.

병행: 커널 트랙(M1, M4, M5)은 `lol/hol/`과 `src/LoL/`, 엔진 트랙(H1–H4)은 `src/Hol/V1`과 `src/X`라서 파일이 겹치지 않는다.

## 11. 게이트

| 게이트 | 시점 | 통과 조건 | 실패 시 |
|--------|------|-----------|---------|
| G0 | M0 끝 | 명세 승인 | 명세 수정. 코드는 시작하지 않는다 |
| G1 | M3 끝 | PTS 핵심에서 Rocq 대조 위반 0건. 선언 100개짜리 코퍼스의 ground 검사 20초 이내 | 귀납형으로 넘어가지 않는다. 느리면 H1을 먼저 끝낸다 |
| G2 | M5 끝 | 역설 모음 전부 거부, 대응하는 변이는 전부 수락 | guard·positivity 명세를 좁힌다 |
| G3 | M8 끝 | 8.2절 M8의 기준 | ALPHA1을 릴리스하지 않는다 |
| G4 | H3 끝 | 2.4절 표의 빈 곳 해소. `intro`, `apply`, `exact`, `Undo`에 해당하는 세션을 API로 재현 | BETA를 시작하지 않는다 |
| G5 | T2 끝 | tactic이 만든 항이 전부 ground 실행 통과 | tactic을 줄인다 |
| G6 | L3 끝 | flagship 3개가 커널과 Rocq export를 통과 | BETA를 릴리스하지 않는다 |

## 12. 위험

| 위험 | 대응 |
|------|------|
| 커널의 속도와 메모리가 엔진에 묶임 | P2는 해결했다. P3, P4를 ALPHA1의 선행 조건으로 둔다. G1에서 측정한다. 계산이 많은 증명(reflection)은 목표에 넣지 않는다 |
| 엔진의 버그가 커널의 버그가 됨 | 커널이 쓰는 Hol의 범위를 좁힌다(7.3절). Rocq가 모든 증명을 다시 검사한다 |
| guard 조건의 명세 오류로 불건전 | 보수적 정의, Rocq 대조 fuzz, 변이, 역설 모음 |
| hole이 있는 실행에서 엔진이 후보를 생성하며 발산 | `flex` clause를 술어마다 맨 앞에 둔다(명세의 규칙). 작업량 제한으로 발산은 오류가 된다 |
| 증명 모드에서 목표 순서가 elaboration 순서로 고정됨 | 적용 규칙의 순서를 T2에서 정한다. 목표를 골라 푸는 기능이 필요한지는 flagship 증명에서 판정한다 |
| 논리 프로그램의 실패는 사유가 없음 | 커널의 각 검사를 `expect Goal Error` 꼴로 써서 첫 실패를 `print`로 보고한다 |
| snapshot이 깊은 복사라 단계마다 비용이 큼 | T1에서 측정한다. 필요하면 H-트랙에 공유 구조를 추가한다 |
| LGS/PGS가 문법을 감당하지 못함(LALR 충돌) | M2 첫 WP에서 문법 스파이크. 연산자는 파서가 아니라 fixity 후처리로 |
| Rocq 버전 의존 | 9.0.0으로 고정하고 기록 |
| 범위 팽창, 호스트가 커짐 | 13절을 고정한다. 크기 예산을 `test/lol/budget.sh`로 검사한다 |
| 측정 실험이 기계를 죽임 | 9절의 운영 규칙 |

## 13. 범위 밖

코귀납형, 모듈 functor, `SProp`, 원시 projection, 원시 정수·배열, impredicative `Set`, extraction, VM·native 계산, Ltac 호환, `.vo` 호환, setoid rewriting, 커널의 정형 검증, Haskell로 쓴 검사기.
PnVRocqLib의 `Prelude.v`에는 `Class`·`Instance` 선언이 117개 있고 라이브러리 전반이 자동화 tactic(`lia`, `eauto`, `congruence` 등)에 기대므로, 그 라이브러리의 이식은 BETA의 목표가 아니다.
Presburger solver를 증명 항을 내는 `lia`로 만드는 일은 별도 연구 과제다.

## 14. 다음에 할 일

결정의 상태:

1. D1: 커널은 Hol 프로그램이다. 사용자가 정한 방향.
2. D3(승인), D5(승인).
3. D10: 증명 모드는 `elab.hol`을 디버깅 모드로 실행하는 것이고, `_`에서 `debug`를 부른다. 사용자의 원래 설계.
4. D6(승인): hole 채우기는 Hol 프로그램 `elab.hol`이 한다. 범위 고정 표는 처음 승인된 것 그대로다.

M0의 산출물:

1. `doc/LoLCore.txt`: 승인됨(2026-11-11, `doc/LoL_plan_audit_2026_11_11.txt`).
2. `doc/LoLALPHA1.txt`와 한국어판 `doc/LoLALPHA1_ko.txt`: 승인됨(2026-11-11). 승인과 함께 나온 두 가지를 반영했다. (가) guard를 Rocq와 같은 강도로 바꾼다는 약속(`doc/LoLCore.txt` 7.4절). (나) "보류·재시도 없음"은 승인하되 실패 때의 처리를 명시(3.4절, 4장, 7장, 10장의 snapshot).
3. `test/lol/`의 규약: `doc/LoLALPHA1.txt` 9장.

G0을 통과했다.

M1의 진행(2026-11-11, 측정):

- 첫 작업 묶음 완료. `lol/hol/kernel.hol`은 코드 130줄이고(`flex`의 임시 정의를 뺀 뒤) sort, 곱, λ, let, 적용, δ, 지역 정의, 변환과 η, 누적성, `Axiom`·`Definition` 수락, 정규형을 구현한다.
- `test/lol/kernel.sh`가 커널에 Hol 항으로 직접 질의한다. 테스트 95개(`pts` 55, `church` 22, `leibniz` 6, `holes` 11, `hurkens` 1)가 BETA 인터프리터와 V1 일반 엔진에서 모두 통과한다. `holes`는 (K4)의 동작, 곧 hole을 만난 커널이 실패하거나 그대로 돌려주거나 단일화할 뿐 항을 나열하지 않는다는 것을 고정한다. `test/smoke.sh`가 이 스크립트를 같이 돌린다.
- Hurkens 유도는 정상 커널이 `[T-Conv]`로 거부하고, `[S-Type]`을 `Type@{l} : Type@{l}`로 바꾼 변이 커널이 수락한다. V1에서 선언 하나에 0.03–0.04초, 22 MB다. BETA 인터프리터는 같은 실행에서 3 GB 상한을 넘는다. 그래서 변이는 V1에서 돌린다. Rocq 9.0.0도 같은 유도를 거부하고 `Unset Universe Checking` 뒤에는 수락한다.
- 변이 15개가 지정한 테스트에 전부 잡힌다.
- `test/smoke.sh`는 `test/lol/kernel.sh`와 `test/flex/flex.hol`을 포함해 166개가 전부 통과한다(`flex` 내장 뒤의 실행). 가상 메모리 상한(`ulimit -v`)을 걸면 ASan으로 빌드하는 `test/v1/{native,ho_term,higher_native}.sh`가 shadow 메모리를 잡지 못해 중단되므로, smoke는 그 상한 없이 시간 제한만 걸고 돌린다.
- 엔진에 대해 새로 드러난 것(V1 일반 엔진, 측정): 큰 정규형을 짓는 실행이 느리다. Church 수의 곱의 `norm`이 16 × 16에 0.27초·35 MB, 32 × 32에 3.08초·173 MB, 64 × 64에 50.9초·1.06 GB이고 마지막은 `Term allocation failed`로 끝난다. 시간이 결과 크기의 제곱으로 는다. 출력 변수를 채워 가며 큰 항을 짓는 경로이고, 7.1절 P3의 남은 부분으로 보인다(원인은 아직 확인하지 않았다). 2.5절의 `conv (mul 100 100) 10000` 0.65초는 출력 항을 짓지 않는 변환 검사라서 이 문제가 드러나지 않았다. BETA 인터프리터는 8 × 8에서 이미 3 GB 상한을 넘는다.
- `flex`를 Hol에 내장했다(사용자 지시, 2026-11-11). `flex T`는 T의 머리가 묶이지 않은 논리 변수일 때 성립하고 아무것도 묶지 않는다. BETA는 `Hol.BETA.Runtime`의 원시 술어로, V1은 C 실행기의 기호 역할 22번으로 구현했고 호스트 정지를 거치지 않는다. 명세는 `doc/HolBETA.txt` 3.6절과 10.6절, `doc/HolV1.txt`. 테스트는 `test/flex/flex.hol`(16개 질의, BETA와 V1 strict가 같은 답)과 C 실행기 fixture 8개.
- 내장의 효과(V1, 측정, 같은 질의): 변환 위주 실행 10.8초 → 4.0초, Church 수 32 × 32의 `norm` 3.08초 → 2.61초, 64 × 64는 50.9초 → 47.3초(여전히 `Term allocation failed`). 임시 정의를 `flex M :- fail.`로 바꿔 어림한 값(7.4초)보다 낫다. 사용자 술어를 부르는 비용까지 없어지기 때문이다.
- 엔진 쪽에 남은 큰 일은 P3(위의 제곱 증가)이고, M4 전에 한다.
- 구현하면서 `doc/LoLALPHA1.txt` 5장과 9장을 실물에 맞췄다: (K1)의 주석 범위, (K3)의 cut 위치에 사실 조회 추가, (K4)에서 보조 술어 제외, 보고의 꼴 `rep L Ts`, `test/lol/kernel/`과 변이 파일.
- 호스트를 만들었다(2026-11-11 04:27). `src/LoL/Core.hs`(코드 47줄, Core 항), `src/LoL/Hol/Embed.hs`(95줄, Core ↔ Hol 항, 사실·목표·보고), `src/LoL/Hol/Session.hs`(122줄, ground 실행과 세 판정), `src/LoL/Env.hs`(105줄, 선언의 수락, 의존 선언의 사실만 주입, Assumptions, 타입·정규형 질의). 합계 369줄이고 환원·변환·단일화·타입 규칙은 없다.
- 호스트 테스트 `test/lol/host.sh`(측정: 깨끗한 빌드 포함 24초, 실행 2.7초·110 MB): 생성한 항 2000개의 Core ↔ Hol 왕복, 그중 40개의 엔진 왕복, 규칙 라벨이 맞는 수락·거부, 정리는 풀리지 않고 정의는 풀림, 사실 주입의 범위, Assumptions, R1(논리 변수가 있는 질의는 실행하지 않음), R3(논리 변수나 잔여 제약이 남은 답은 수락이 아님), R5(시간 한도와 작업량 한도는 미결, 그 뒤에도 커널을 계속 쓸 수 있음). `let`의 정의와 타입을 양방향에서 같이 바꾼 embedding(왕복은 통과함)이 테스트에 걸리는 것도 확인했다.
- `test/smoke.sh`는 `test/lol/host.sh`를 포함해 167개가 전부 통과한다(2026-11-11 04:28).
- M1의 완료 기준을 모두 채웠다(2026-11-11 04:27). `ppap.cabal`에 등록할 모듈: `LoL.Core`, `LoL.Env`, `LoL.Hol.Embed`, `LoL.Hol.Session`(등록 전에도 테스트는 `-isrc`로 직접 컴파일한다).
- 다음은 M2(표면 구문과 명시적 번역)다. 엔진의 P3(큰 정규형의 제곱 증가)은 M4 전에 한다.

M1 다지기: 엔진 최적화(2026-11-11, 사용자 지시 "오늘은 최적화만을 한다. M1을 다지는 것이다". 측정은 모두 V1 일반 엔진, 같은 기계, 프로세스 전체를 `/usr/bin/time`으로 1회):

- **P3을 고쳤다(2026-11-11 17:59).** 큰 정규형이 제곱으로 느려지던 원인은 둘이었다.
    - (가) `=` 목표마다 호스트로 나갔다. 기계는 양변을 통째로 내보내고 Haskell은 그것을 해독한 뒤 "산술이 없으니 탐색에 맡긴다"고 답했다. 내보낸 변수는 수집되지 않으므로 메모리도 제곱으로 남았다.
    - (나) C의 항 저장소는 변수도 nominal도 지표도 없는 항(ground)만 건너뛰었다. `pi x\` 아래에서 지은 항에는 nominal이 있으므로, 변수를 그런 항에 묶을 때마다 정규화·복사·η 축약·occurs 검사·scope 낮추기가 각각 항 전체를 훑었다.
- 고친 내용:
    - 항 저장소의 노드마다 요약을 둔다. 변수·와일드카드·불투명 기호가 아래에 없는 노드는 "안정"하고, 안정한 노드는 β 정규 여부, η 정규 여부, 산술 기호 포함 여부, nominal의 최대 scope, 열린 지표의 상한을 안다. 순회는 요약으로 답이 나오면 그 부분항에 들어가지 않고, 변수를 안정한 항에 묶을 때는 복사 없이 공유한다. 노드는 56바이트에서 64바이트가 되었다.
    - 단일화는 두 항을 한 번만 정규화하고, rigid 항의 인자를 내려갈 때마다 다시 정규화하거나 다시 비교하지 않는다. 마지막 인자와 λ의 몸은 재귀 없이 반복으로 푼다.
    - 타입이 `nat`이 아니고 양변에 산술 기호가 없는 `=`와, 전건이 보통 술어의 원자·clause의 연언인 `=>`는 기계가 호스트 정지 없이 처리한다. 호스트가 상태를 보지 않고 하던 답과 같다. 기호 역할 23(`+ - * /`)과 24(타입 `nat`)를 더했다.
    - 그 결과 커널의 실행은 `print`나 답에 이를 때까지 호스트 정지가 0회다.
- 측정. `norm (mul n n)`, n은 본문이 리터럴인 Church 수, 결과는 깊이 n²인 수:

    | n | 수정 전 | 수정 후 |
    |---|---------|---------|
    | 16 | 0.09 s / 27 MB | 0.02 s / 22 MB |
    | 32 | 2.41 s / 127 MB | 0.04 s / 27 MB |
    | 48 | 26.57 s / 664 MB | 0.06 s / 28 MB |
    | 64 | 실패(약 47초 뒤 `Term allocation failed`, 1 GB) | 0.10 s / 33 MB |
    | 80 | 실행하지 않음 | 0.15 s / 38 MB |
    | 90 | 실행하지 않음 | 0.21 s / 42 MB |
    | 96 | 실행하지 않음 | 오류: 깊이 한계 8192(P4) |

    수정 후 시간은 결과 크기에 비례한다. C 실행기만 따로 돌리면 n = 90(결과 깊이 8100)이 0.18초다.
- 다른 경로도 느려지지 않았다. 부록 A의 probe(단항 수, 순수 논리)는 `conv (mul 100 100) 10000`이 0.58초에서 0.36초, `conv (mul 200 200) 40000`이 2.24초에서 1.39초다. 목표 B1(0.5초 이내)을 채웠다. 산술 서비스를 쓰는 `num 10000`은 0.14초로 같다. 기존 C fixture 전체의 실행 시간도 같다(31.9 ms와 31.6 ms).
- 테스트: 항 저장소 단위 테스트 3개(nominal로 된 1만 원소 리스트를 방문 64회 예산 안에서 묶기·scope 위반·추상화·치환, η 요약, 산술 표시), 기계 fixture 10개(`=`와 `=>`의 종류별 호스트 정지 횟수, 아래에서 위로 지은 리스트를 연산당 방문 256회 예산으로 실행), `test/lol/host.sh`에 64 × 64의 정규형이 4096의 수와 같다는 검사(아래 P4에서 128 × 128로 키웠다). `test/smoke.sh`는 167개가 전부 통과한다(엔진 수정 뒤의 실행).
- 남은 것(P3의 범위 밖, 측정으로 확인):
    - 변수가 남아 있는 항은 여전히 묶을 때마다 그 부분을 다시 짓는다. hole이 있는 항을 다루는 elaborator(BETA)에서 드러날 것이다.
    - 출력을 머리에서 꼬리로 짓는 프로그램(`num N (succ M) :- ..., num K M.`)의 결과는 변수 링크가 남아 안정되지 않는다. 쓸 때마다 전체를 훑는다(이때는 깊이 한계에도 걸렸고, 그 한계는 아래 P4에서 없앴다).
    - binder 하나를 드나들 때마다 그 변수가 나오는 경로를 따라 항을 다시 짓는다(HOAS의 치환과 추상화). binder가 d겹이고 몸이 크면 d배가 든다.
- P3을 고친 직후의 병목(측정, 2026-11-11 17:59). 아래 두 항목에서 이어서 다뤘다.
    - P4: 결과의 깊이가 8192를 넘으면 `Term nesting exceeds the native work stack`으로 끝난다(96 × 96, binder를 나올 때의 추상화 `bind_value`). 단항 수 8192 이상, 원소 8192개 이상의 리스트가 같은 한계에 걸린다.
    - P5: 선언 하나의 ground 실행에 9.3 ms가 드는데, 그중 7.0 ms가 커널 clause를 질의마다 다시 컴파일하는 비용이다(메타데이터 0.55 ms, 바이트코드 검증 0.66 ms가 두 번, 기계 생성과 실행 0.1 ms).
- **P4를 고쳤다(2026-11-11 18:35).** 항의 깊이는 C 스택이 아니라 메모리가 정한다.
    - 치환(지표의 이동·대입·동시 구체화·binder 제거), 정규화, η 축약, 변수의 값 짓기(매개변수에 대한 추상화), occurs 검사, scope 낮추기, 지표 검사, 동등 비교, 산술 검사를 재귀 대신 항 저장소의 프레임 배열로 돈다. 재귀가 남은 곳은 셋이고 한계 8192도 거기에만 남는다: 원시 항 wire의 import, export의 함수 쪽, 단일화에서 rigid 항의 마지막이 아닌 인자.
    - 깊이가 커지자 수집기의 비용이 드러났다. 수집이 식별자를 하나씩 폐기하면서 폐기 구간 배열을 매번 밀었고, 256 × 256 한 번에 누적 289 GB를 옮겼다. 한 번의 수집이 폐기하는 식별자를 정렬된 한 번의 병합으로 넣게 해서 11 MB가 되었다(C 실행기 단독 2.99초 → 1.44초).
    - 측정(같은 벤치마크):

        | n | 결과의 깊이 | 수정 전 | 수정 후 |
        |---|-------------|---------|---------|
        | 96 | 9216 | 오류(깊이 한계) | 0.19 s / 41 MB |
        | 128 | 16384 | 오류 | 0.33 s / 54 MB |
        | 256 | 65536 | 오류 | 1.54 s / 154 MB |
        | 316 | 99856 | 오류 | 2.31 s / 223 MB |

        목표 B3(깊이 10⁵인 항)에 해당하는 크기까지 시간이 크기에 비례한다. 머리에서 꼬리로 지은 단항 수 10000과의 변환(`num 10000 T` 뒤 `conv (mul 100 100) T`)도 오류에서 0.49초가 되었다.
    - 대가: 얕은 항에서는 프레임 배열이 재귀보다 조금 느리다. 단항 수 변환 probe가 C 실행기 단독으로 0.32초에서 0.34초다(프로세스 전체 0.36초 → 0.39초, 목표 B1의 0.5초 이내는 유지).
    - 형식이 맞지 않는 원시 항의 끝나지 않는 환원은 이제 깊이 한계가 아니라 작업량 한계에서 멈춘다.
    - 테스트: 깊이 20만인 항에 대한 치환·추상화·변수 링크를 따라가는 정규화·occurs 검사·비교·η 축약·export, 수집이 폐기한 식별자의 만료 검사, `test/lol/host.sh`의 128 × 128 정규형(깊이 16384)과 그 변환·거부.
- **선언당 고정 비용을 줄였다(2026-11-11 18:35, P5의 일부).** 호스트는 커널을 불러올 때 커널의 clause를 한 번만 컴파일하고(`prepareFullProgram`), 선언마다 그 위에 질의와 의존 선언의 사실만 컴파일한다(`compilePreparedProgram`).
    - 재다가 찾은 것: 두 컴파일러(`FullCompiler`, `Compiler`)가 새 템플릿의 번호를 `IntMap.size`로 얻었는데 이 함수는 O(n)이라 컴파일이 템플릿 수의 제곱이었다. 키 map의 크기(O(1))로 바꿨다. 바이트코드 검증기도 자연수 리터럴마다 payload 리스트를 처음부터 걸어서 제곱이었고, 한 번 만든 집합을 보게 했다. 기계는 자연수 인자가 서로 다른 clause를 시도 없이 건너뛴다(`cst_type N A`의 조회).
    - 측정(호스트 API로 작은 정의를 연달아 선언):

        | 실험 | 수정 전 | 수정 후 |
        |------|---------|---------|
        | 서로 독립인 선언 800개 | 6.76 s (선언당 8.5 ms) | 0.72 s (선언당 0.9 ms) |
        | 앞의 것에 의존하는 선언 200개 사슬 | 3.99 s | 0.55 s |
        | 같은 사슬 400개 | 13.9 s | 2.08 s |
        | 같은 사슬 800개 | 62.8 s | 9.6 s |

        의존 선언이 800개인 실행 하나의 단계별 비용은 컴파일 183 ms → 27 ms, 검증 13 ms → 4.2 ms, 기계 생성과 실행 12 ms → 7.5 ms다.
    - `test/lol/kernel.sh`의 V1 실행(테스트 95개, 질의마다 커널을 컴파일하는 REPL 경로)도 4.26초에서 1.46초가 되었다.
    - 테스트: `test/v1/full_compiler.sh`가 미리 컴파일한 프로그램과 한꺼번에 컴파일한 프로그램을 clause·질의·변수·기호·환경으로 대조한다(전부 미리, 절반만 미리 두 경우). 자연수 리터럴 3001개짜리 프로그램, 자연수로 제외되는 clause의 fixture 둘.
    - `test/smoke.sh`는 167개가 전부 통과한다(2026-11-11 18:38, 이 묶음까지 넣은 실행).
    - 남은 것: 사슬은 여전히 제곱이다. 선언마다 의존 선언 전부의 사실을 다시 컴파일하고 검증하고 기계에 싣기 때문이다(계획한 우회: 7.1절 P5). 이것을 없애려면 기계가 프로그램을 유지한 채 사실과 질의만 더 받는 구조(P5)와 첫 인자 색인(P6)이 필요하고, 호스트의 `Env`가 순수 값이라는 점(가지치기한 환경이 공존한다)과 맞춰 설계해야 한다. Hol V2의 일로 남긴다.

- **P5와 P6을 했다(2026-11-11 19:43).** 기계는 프로그램을 유지하고, 사실은 첫 인자로 찾는다.
    - 결정(사용자, 2026-11-11): `Env`는 값으로 남고 기계는 그 캐시다. 세 안 중 (나) "기계 하나를 공유하고 가지치기를 금지"는 기각, (가) "`Env` 판마다 기계"는 메모리 때문에 택하지 않음, (다) "`Env`가 진실이고 기계는 캐시"를 택했다. `doc/LoLALPHA1.txt` 5.2절은 처음에는 고치지 않기로 했다가, 같은 날 19:57에 사용자가 고치기로 했다("명세 5.2절 바꾸자"). 두 판의 마지막 문단을 "실행은 한 환경의 사실을 본다. 호스트는 그것을 실어 둔 채로 두어도 되고 의존 선언의 사실만 주어도 된다"로 바꿨다.
    - 엔진(C): 기계가 wordcode를 조각으로 받는다. `hol_v2_extend`는 조각의 기호와 clause를 프로그램 뒤에 붙이고, `hol_v2_query`는 조각의 질의를 한 번 실행하고, `hol_v2_idle`은 실행을 떠난다. 조각의 템플릿·clause·숫자는 0부터 번호를 매기고, 기호와 주석만 기계의 표에 이어진다. 그래서 기계는 템플릿 표를 들고 있지 않는다.
    - 실행을 떠나면 기계는 같은 프로그램으로 새로 만든 기계와 같은 상태가 된다: 묶임을 되돌리고, 프로그램 위의 힙·연속·선택점·지속 대입·질의가 더한 기호·실행의 식별자를 버리고, 작업 한계·수집 간격·디버깅을 기본값으로 돌린다. 다음 실행은 변수·호출·호스트 상태를 같은 번호로 센다. 떠난 실행의 snapshot은 복원이 거부된다.
    - 색인(C): 머리가 "술어를 인자에 적용한 꼴"인 사실은 첫 인자가 자연수 리터럴이거나 보통 상수가 머리인 항이면 열쇠를 갖는다. 같은 종류의 열쇠를 가진 호출은 열쇠가 같은 사실과 열쇠 없는 사실만 원래 순서로 본다. 색인이 빼는 사실은 기존의 "시도 없이 건너뛰기"가 건너뛰던 사실뿐이므로 답과 순서는 같다. 열쇠가 두 종류이거나 인자 수가 다른 술어는 색인 없이 전부 본다.
    - 컴파일러(Haskell): `loadPreparedProgram`, `extendLoadedProgram`, `queryLoadedProgram`이 조각을 낸다. 호스트가 유지하는 것은 기호 표와 주석 표뿐이고 그 크기는 사실의 수와 무관하다. 조각끼리는 템플릿을 공유하지 않는다.
    - 런타임(Haskell): `Full.Engine`(`createEngine`, `extendEngine`, `withQuery`, `leaveEngine`, `closeEngine`). 질의마다 여는 세션은 지금의 세션과 같은 것이고, 질의 변수의 식별자가 기계가 알려 주는 번호에서 시작한다는 점만 다르다.
    - 호스트: `Kernel`이 엔진 하나를 든다. 엔진은 커널과 한 환경의 사실 전부를 들고, 그 환경의 도장(stamp)을 기억한다. 선언이 있는 환경마다 도장이 하나씩 있고 `declare`만 도장을 만든다. 실행은 엔진의 도장이 자기 환경의 것이면 그대로 돌고, 아니면 엔진을 버리고 그 환경의 선언에서 다시 짓는다(512개 사실씩 나눠 싣는다). 수락된 선언은 사실 한두 개를 엔진에 더하고 도장을 새 환경의 것으로 바꾼다. 오류가 난 엔진, 시간 제한에 걸린 엔진은 버린다. `Env`는 생성자를 내보내지 않는 추상 타입이 되었다(도장을 위조할 수 없게).
    - 지금까지의 경로는 `Reference` 모드로 남겼다(`declareIn`, `askIn`): 실행마다 새 기계를 만들고 의존 선언의 사실만 준다. 테스트가 두 경로의 판정을 대조한다.
    - 측정(작은 정의를 연달아 선언. 같은 하니스에서 `Reference`와 `Persistent`):

        | 실험 | 실행마다 새 기계 | 엔진 하나 |
        |------|------------------|-----------|
        | 서로 독립인 선언 800개 | 0.68 s (선언당 0.85 ms) | 0.17 s (선언당 0.21 ms) |
        | 앞의 것에 의존하는 선언 200개 사슬 | 0.31 s | 0.03 s |
        | 같은 사슬 400개 | 1.04 s | 0.06 s |
        | 같은 사슬 800개 | 3.96 s | 0.12 s |
        | 같은 사슬 1600개 | 18.4 s | 0.24 s |
        | 같은 사슬 12800개 | 실행하지 않음 | 1.9 s / 60 MB |
        | 같은 사슬 51200개 | 실행하지 않음 | 7.6 s / 170 MB |

        사슬의 선언당 비용은 길이와 무관하게 0.15 ms다. (이 사슬은 2026-11-11 18:35의 표에 쓴 사슬과 선언의 모양이 다르다. 그 하니스는 남아 있지 않아 새로 짰다.) 사슬 12800개의 마지막 고리를 정규화하면 정의 12800개를 차례로 펼치는데 0.10초다. 엔진이 들지 않은 환경으로 돌아가는 비용은 선언 12800개에 0.10초, 51200개에 0.43초다(선언당 약 8 μs).
    - 다른 경로: 색인은 사실 표가 없는 실행에도 듣는다. 커널의 clause가 첫 인자의 생성자로 골라지기 때문이다. C 실행기 단독으로 `mul 256 256`의 정규형이 1.51초에서 1.37초, 단항 수 변환 probe가 0.38초에서 0.35초다. `test/lol/kernel.sh`의 V1 실행은 1.5초 안팎으로 같다.
    - 테스트: 질의 변수를 쓰지 않는 C fixture 전부를 조각으로도 실행한다(씨앗, 두 번의 추가, 질의 세 번. 한 번은 도중에 떠난 실행 뒤). 잘못된 조각과 할당 실패, 6000행 표 둘의 마지막 행 조회, 질의가 있는 기계에 다시 질의하기, 저장소의 `ht_reset` 단위 테스트. `test/v1/full_compiler.sh`는 조각을 해독해 통째로 컴파일한 프로그램과 대조하고, `test/v1/full_runtime.sh`는 엔진과 새 기계의 답을 프로그램이 자라기 전후로 대조한다. `test/lol/host.sh`는 상수 7이 공리·수·정리인 세 가지를 섞어 물으면서 엔진과 새 기계의 판정을 대조하고, 300개 사슬과 더 오래된 환경을 번갈아 쓴다. `test/smoke.sh`는 167개가 전부 통과한다(2026-11-11 19:43).
    - 남은 것:
        - 엔진은 환경 하나만 든다. 환경을 오가면 갈 때마다 다시 싣는다. 증명 모드의 되돌리기처럼 자주 오가게 되면 "앞부분이 같은 환경으로는 잘라 내고 이어 싣기"가 필요하다. 지금은 사실을 뺄 수 없다.
        - 엔진의 힙은 선언 사이에 항을 공유하지 않는다. 작은 선언 하나에 약 3 kB다(Haskell 쪽 값 포함).
        - 수집은 프로그램 전체를 훑는다. 환경이 크면 긴 실행의 수집마다 그만큼 든다(사슬 51200개의 마지막 고리 정규화가 0.75초로, 12800개의 4배가 아니라 7배다).
        - REPL은 여전히 질의마다 모듈 전체를 컴파일한다. `Full.Engine`을 쓰면 없어진다.
        - (해결, 2026-11-11 19:57) 명세 5.2절의 "실행 하나는 ... 검사할 선언이 의존하는 선언들의 사실을 받는다"는 `Reference` 모드의 설명이었다. 엔진은 환경의 사실 전부를 들고 있고, 커널이 상수를 번호로 조회하므로 실행이 닿는 사실은 같다. 사용자의 결정으로 두 판의 문단을 두 방식을 다 허용하는 말로 고쳤다.

남은 최적화 작업(2026-11-11 19:57에 모음. 위 항목들의 "남은 것"을 한곳에 모은 목록이고, 번호는 그날 사용자에게 보고한 순서다. "측정"이 없는 칸은 재지 않은 것이다):

| # | 작업 | 근거 | 권하는 시점 | 상태 |
|---|------|------|-------------|------|
| O1 | REPL(`V1 --test`, V1 대화형)이 질의마다 모듈 전체를 다시 컴파일한다. `Full.Engine`을 쓰면 모듈은 한 번만 싣는다 | 측정: `test/lol/kernel.sh`의 V1 실행이 테스트 95개에 1.5초 | Hol V2 | 안 함 |
| O2 | 수집이 프로그램 전체를 훑는다. 변수가 없는 프로그램 부분은 표시도 이동도 필요 없다 | 측정: 사슬 51200개의 마지막 고리 정규화가 0.75초로, 12800개(0.10초)의 4배가 아니라 7배 | 지금 | 됨(2026-11-11 20:23): 0.36초, 12800개(0.09초)의 4배 |
| O3 | 엔진은 환경 하나만 든다. 다른 환경으로 갈 때마다 그 환경을 다시 싣는다. "앞부분이 같으면 잘라 내고 이어 싣기"가 없고, 실은 사실을 뺄 수 없다 | 측정: 선언당 약 8 μs(12800개 0.10초, 51200개 0.43초) | 증명 모드의 되돌리기(BETA) 전 | 안 함 |
| O4 | 변수가 남아 있는 항은 묶을 때마다 그 부분을 다시 짓는다. 머리에서 꼬리로 지은 구조는 변수 링크가 남아 안정되지 않는다. binder를 드나들 때마다 그 변수가 나오는 경로를 다시 짓는다 | P3을 고칠 때 확인(14절) | hole이 있는 항을 다루는 elaborator(BETA) | 안 함 |
| O5 | 엔진의 상수 배: clause의 꼴을 시도마다 다시 읽는 것, 목표마다 spine을 할당하는 것 등 | 추정 5~10%. 재지 않음 | 지금 | 됨(2026-11-11 20:23): C 실행기 단독으로 변환 probe −30%, `mul 256 256` −14%. 남은 것은 아래 O12 |
| O6 | 깊이 한계 8192가 남은 순회 셋(원시 항 wire의 import, export의 함수 쪽, 단일화에서 rigid 항의 마지막이 아닌 인자). 부록 A의 probe를 `test/v1/`의 회귀 벤치마크로 편입 | P4를 고칠 때 남김(14절) | 지금 | 됨(2026-11-11 20:23): 한계가 남은 순회가 없다. `test/v1/probe.sh` |
| O7 | 엔진의 힙은 선언 사이에 항을 공유하지 않는다 | 측정: 작은 선언 하나에 약 3 kB(Haskell 쪽 값 포함), 51200개에 170 MB | 큰 라이브러리 | 안 함 |
| O8 | 호스트가 제약이나 산술 전제를 들고 있는 프로그램은 정지마다 상태 전체를 내보낸다. 내보낸 변수의 식별자는 해제되지 않는다(P1의 남은 것) | `doc/HolV1.txt`의 2026-11-11 기록 | 레벨 제약(BETA) | 안 함 |
| O9 | 증명 단계의 snapshot이 프로그램까지 통째로 복사한다 | 측정: 기계 clone이 선언 800개에 0.09 ms, 8000개에 1.4 ms | 증명 모드(BETA) | 안 함 |
| O10 | 색인은 첫 인자 하나만 본다(`con_type B I J`는 `B`까지만). 지역 가정은 선형 탐색이다 | 재지 않음 | 귀납형이 들어온 뒤(M4~) 측정해서 | 안 함 |
| O11 | 선언당 0.15 ms의 내역을 모른다(조각 컴파일, 검증, 세션 열기, 답 해독 중 어느 것인지) | 재지 않음 | 선언 수가 10⁵을 넘길 때 | 안 함 |
| O12 | 식별자 표: 새 변수마다 해시 표에 넣고, 수집과 되돌리기 때마다 하나씩 뺀다. 호스트에 내보낸 식별자만 표에 넣으면 대부분 없어지지만 "만료된 식별자" 검사의 뜻이 바뀐다 | gprof로 변환 probe의 10~15%(추정. `-pg` 빌드라 부정확) | 엔진을 다시 손볼 때 | 안 함 |

- **O2, O5, O6을 했다(2026-11-11 20:23, 사용자 지시 "2번, 5번과 6번을 완료하면").** 위 표의 세 줄이다.
    - O2. 프로그램에서 첫 변수 앞의 노드는 적재할 때 봉인한다(`ht_seal`). 어떤 묶임도 그 노드가 더 젊은 노드를 가리키게 할 수 없으므로, 수집은 봉인된 부분을 표시하지도 옮기지도 않고 그만큼의 배열도 잡지 않는다. 조각으로 받은 프로그램에는 변수가 없으므로 전부 봉인된다. 상태 전체를 내보내는 정지도 봉인된 부분을 훑지 않는다. 측정: 사슬 51200개의 마지막 고리 정규화 0.75초 → 0.36초(12800개는 0.10초 → 0.09초).
    - O5. gprof로 변환 probe를 재서 고른 것들이다.
        - 전역 사실의 clause 꼴(앞의 binder 수, 머리, 몸, 머리의 rigid 상수와 인자 수)은 적재할 때 한 번 읽는다. 머리가 rigid인 literal 꼴은 어떤 묶임으로도 바뀌지 않기 때문이다. 시도마다 하던 꼴 읽기가 63만 번에서 62번이 되었고, 그런 사실의 머리는 구체화한 뒤 다시 정규화하지 않는다. 지역 가정과, 적재 때 머리가 flexible이던 사실은 전처럼 매번 읽는다.
        - 탐색은 EXEC 루프가 이미 구한 목표의 spine을 그대로 쓴다(목표마다 정규화와 spine이 한 번씩 줄었다).
        - spine의 인자가 6개 이하이면 spine 안에 둔다(할당 없음). 단일화는 식 목록과 binder 힌트 배열을 저장소에 두고 다시 쓴다.
        - 식별자 표는 직전 수집 주기에 필요했던 크기를 유지한다(수집마다 줄였다가 다시 키우던 것을 없앰).
        - 정규화: 적용의 완전 정규형을 구할 때 함수 쪽을 WHNF로 한 번, 다시 처음부터 NF로 한 번 훑었다. WHNF로 얻은 것은 머리에 redex가 없는 spine이므로 그 spine의 인자만 정규화하면 된다. 인자가 n개인 적용의 정규화가 n²에서 n이 되었다(변수가 든 인자 2만 개짜리 적용: 0.79초 → 0.001초. 옛 엔진도 0.97초였다). O6의 테스트가 찾은 것이다.
        - 측정(C 실행기 단독, 같은 wordcode, 7회 중앙값): 변환 probe 0.37초 → 0.26초, `mul 256 256`의 정규형 1.40초 → 1.20초. 프로세스 전체로는 `conv (mul 100 100) 10000`이 0.39초 → 0.28초, `conv (mul 200 200) 40000`이 1.4초 → 1.06초, `mul 128 128`의 정규형이 0.36초 → 0.29초.
    - O6. 남아 있던 재귀 순회 셋을 반복으로 바꿨다. 항 wire의 import와 export는 저장소의 프레임 배열로 돌고, 단일화는 rigid 항의 인자 쌍을 배열에 쌓아 두고 앞에서부터 푼다(쌍마다 그 위의 binder 수를 같이 둔다. 푸는 순서는 전과 같다). `TERM_DEPTH_LIMIT`은 없어졌고 어떤 항 연산도 깊이를 제한하지 않는다.
    - 부록 A의 probe를 `test/v1/probe.sh`로 넣었다. 변환 셋, 산술로 세기, 커널에서 `mul 128 128`의 정규형(깊이 16384)을 2026-11-11 측정값의 약 10배인 시간 예산과 주소 공간 2 GiB 안에서 돌린다. 제곱 시간이나 메모리 폭주가 돌아오는 것을 잡는 용도이고 작은 느려짐은 잡지 못한다.
    - 테스트: 봉인된 프로그램 20만 노드 위의 수집이 16 kB 넘게 할당하지 않는지, 첫 성분으로 20만 번 중첩된 쌍과 인자 20만 개짜리 적용의 export·import·단일화. 기존 C fixture 127개(수집을 목표마다 하는 실행 포함), HOPU 대조 214건, 호스트·런타임 테스트가 그대로 통과한다. `test/smoke.sh`는 168개가 전부 통과한다(2026-11-11 20:22).
    - 끝난 뒤의 수치(프로세스 전체): 사슬의 선언당 비용이 0.15 ms에서 0.13 ms(12800개 1.70초 / 58 MB, 51200개 6.9초 / 163 MB), 독립 선언은 0.21 ms로 같다. 사슬의 마지막 고리 정규화는 12800개 0.07초, 51200개 0.30초. `mul 256 256`의 정규형 1.30초, `mul 316 316`(깊이 99856) 2.05초 / 223 MB. `test/lol/kernel.sh`의 V1 실행은 1.5초로 같다.

H1의 P3과 P4는 끝났다.

`codex.md`의 `LoL ALPHA1`, `Hol V2`, `LoL BETA` 항목은 사용자가 이 문서를 가리키도록 갱신한다.

기록 규칙: 2026-11-11 04:27부터 이 문서의 기록에는 시와 분까지 적는다(KST). 그 전의 기록은 날짜만 있다.

## 부록 A. probe 소스

`V1 --test --general`과 `Hol --test`에서 실행했다. 모듈 로더가 현재 디렉터리를 프로젝트 루트로 보므로 파일이 있는 디렉터리에서 실행한다.

### A.1 커널 (2.2절)

```
kind tm type.

type prop tm.
type typ (nat -> tm).
type prod (tm -> (tm -> tm) -> tm).
type lam (tm -> (tm -> tm) -> tm).
type app (tm -> tm -> tm).
type nat_ty tm.
type zero tm.
type succ (tm -> tm).
type nat_elim (tm -> tm -> tm -> tm -> tm).
type eq (tm -> tm -> tm -> tm).
type refl (tm -> tm -> tm).
type eq_elim (tm -> tm -> tm -> tm -> tm -> tm -> tm).
type add tm.
type mul tm.

type unfold (tm -> tm -> o).
type typeof (tm -> tm -> o).
type whnf (tm -> tm -> o).
type whnf_app (tm -> tm -> tm -> o).
type whnf_nat_elim (tm -> tm -> tm -> tm -> tm -> o).
type whnf_eq_elim (tm -> tm -> tm -> tm -> tm -> tm -> tm -> o).
type conv (tm -> tm -> o).
type conv_whnf (tm -> tm -> o).
type of (tm -> tm -> o).
type sort_of (tm -> tm -> o).
type rule (tm -> tm -> tm -> o).
type check (tm -> tm -> o).

unfold add (lam nat_ty (m\ lam nat_ty (n\ nat_elim (lam nat_ty (x\ nat_ty)) n (lam nat_ty (k\ lam nat_ty (ih\ succ ih))) m))).
typeof add (prod nat_ty (x\ prod nat_ty (y\ nat_ty))).
unfold mul (lam nat_ty (m\ lam nat_ty (n\ nat_elim (lam nat_ty (x\ nat_ty)) zero (lam nat_ty (k\ lam nat_ty (ih\ app (app add n) ih))) m))).
typeof mul (prod nat_ty (x\ prod nat_ty (y\ nat_ty))).

whnf (app M N) R :- !, whnf M M1, whnf_app M1 N R.
whnf (nat_elim P Z S N) R :- !, whnf N N1, whnf_nat_elim N1 P Z S R.
whnf (eq_elim A X P D Y E) R :- !, whnf E E1, whnf_eq_elim E1 A X P D Y R.
whnf C R :- unfold C B, !, whnf B R.
whnf M M.

whnf_app (lam A F) N R :- !, whnf (F N) R.
whnf_app M N (app M N).

whnf_nat_elim zero P Z S R :- !, whnf Z R.
whnf_nat_elim (succ K) P Z S R :- !, whnf (app (app S K) (nat_elim P Z S K)) R.
whnf_nat_elim N P Z S (nat_elim P Z S N).

whnf_eq_elim (refl B W) A X P D Y R :- !, whnf D R.
whnf_eq_elim E A X P D Y (eq_elim A X P D Y E).

conv M M :- !.
conv M N :- whnf M M1, whnf N N1, conv_whnf M1 N1.

conv_whnf M M :- !.
conv_whnf (prod A F) (prod B G) :- conv A B, pi x\ conv (F x) (G x).
conv_whnf (lam A F) (lam B G) :- conv A B, pi x\ conv (F x) (G x).
conv_whnf (app M N) (app M1 N1) :- conv_whnf M M1, conv N N1.
conv_whnf (succ M) (succ N) :- conv M N.
conv_whnf (nat_elim P Z S N) (nat_elim P1 Z1 S1 N1) :- conv_whnf N N1, conv P P1, conv Z Z1, conv S S1.
conv_whnf (eq A X Y) (eq A1 X1 Y1) :- conv A A1, conv X X1, conv Y Y1.
conv_whnf (refl A X) (refl A1 X1) :- conv A A1, conv X X1.
conv_whnf (eq_elim A X P D Y E) (eq_elim A1 X1 P1 D1 Y1 E1) :- conv_whnf E E1, conv A A1, conv X X1, conv P P1, conv D D1, conv Y Y1.

rule SA prop prop.
rule prop (typ J) (typ J).
rule (typ I) (typ J) (typ J) :- I =< J.
rule (typ I) (typ J) (typ I) :- I > J.

sort_of A S :- of A T, whnf T S, rule S prop prop.

of prop (typ 0).
of (typ I) (typ J) :- J is I + 1.
of (prod A F) S :- sort_of A SA, (pi x\ of x A => sort_of (F x) SB), rule SA SB S.
of (lam A F) (prod A G) :- sort_of A SA, pi x\ of x A => of (F x) (G x).
of (app M N) T :- of M TM, whnf TM (prod A G), of N TN, conv TN A, T = G N.
of nat_ty (typ 0).
of zero nat_ty.
of (succ N) nat_ty :- check N nat_ty.
of (nat_elim P Z S N) (app P N) :- check N nat_ty, of P TP, whnf TP (prod PA PG), conv PA nat_ty, (pi x\ of x nat_ty => sort_of (app P x) SP), check Z (app P zero), check S (prod nat_ty (k\ prod (app P k) (ih\ app P (succ k)))).
of (eq A X Y) prop :- check A (typ 0), check X A, check Y A.
of (refl A X) (eq A X X) :- check A (typ 0), check X A.
of (eq_elim A X P D Y E) (app (app P Y) E) :- check A (typ 0), check X A, check P (prod A (y\ prod (eq A X y) (e\ prop))), check D (app (app P X) (refl A X)), check Y A, check E (eq A X Y).
of C T :- typeof C T.

check M T :- of M T1, conv T1 T.
```

### A.2 측정용 보조 술어 (2.5절)

```
type num (nat -> tm -> o).
type p10 (tm -> tm -> o).
type p100 (tm -> tm -> o).
type neg (o -> o).
type isvar (tm -> o).

num 0 zero.
num N (succ M) :- N > 0, K is N - 1, num K M.
p10 X (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ X)))))))))).
p100 X Y :- p10 X A, p10 A B, p10 B C, p10 C D, p10 D E, p10 E F, p10 F G, p10 G H, p10 H I, p10 I Y.
neg G :- G, !, fail.
neg G.
isvar X :- neg (neg (X = prop)), neg (neg (X = nat_ty)).
```

`forall n, add n 0 = n`의 증명을 검사한 질의:

```
?- check (lam nat_ty (n\ nat_elim (lam nat_ty (k\ eq nat_ty (app (app add k) zero) k)) (refl nat_ty zero) (lam nat_ty (k\ lam (eq nat_ty (app (app add k) zero) k) (ih\ eq_elim nat_ty (app (app add k) zero) (lam nat_ty (y\ lam (eq nat_ty (app (app add k) zero) y) (e\ eq nat_ty (succ (app (app add k) zero)) (succ y)))) (refl nat_ty (succ (app (app add k) zero))) k ih))) n)) (prod nat_ty (n\ eq nat_ty (app (app add n) zero) n)).
```

### A.3 hole 채우기 (2.3절)

A.1과 A.2에 더한 것이다.

```
kind raw type.
kind arg type.
type im arg.
type ex arg.
type rtm (tm -> raw).
type rhd (tm -> raw).
type rapp (raw -> raw -> raw).
type implicits (tm -> list arg -> o).
type spine (raw -> tm -> list raw -> list raw -> o).
type build (list arg -> list raw -> tm -> tm -> tm -> tm -> o).
type elabc (raw -> tm -> tm -> o).
type unify (tm -> tm -> o).
type unify_whnf (tm -> tm -> o).
type feq tm.
type sfn tm.

typeof feq (prod (typ 0) (a\ prod (typ 0) (b\ prod (prod a (z\ b)) (f\ prod a (x\ prod a (y\ prod (eq a x y) (e\ eq b (app f x) (app f y)))))))).
typeof sfn (prod nat_ty (x\ nat_ty)).
unfold sfn (lam nat_ty (x\ succ x)).
implicits feq (im :: im :: ex :: im :: im :: ex :: []).

spine (rhd C) C Acc Acc.
spine (rapp R A) C Acc Args :- spine R C (A :: Acc) Args.

build [] [] M T M T.
build (im :: Mask) Args M T M2 T2 :- whnf T (prod A B), build Mask Args (app M H) (B H) M2 T2.
build (ex :: Mask) (R :: Args) M T M2 T2 :- whnf T (prod A B), elabc R A X, build Mask Args (app M X) (B X) M2 T2.

elabc (rtm M) T M :- of M T1, unify T1 T.
elabc R T M :- spine R C [] Args, typeof C TC, implicits C Mask, build Mask Args C TC M T1, unify T1 T.

unify M N :- M = N, !.
unify M N :- isvar M, !, fail.
unify M N :- isvar N, !, fail.
unify M N :- whnf M M1, whnf N N1, unify_whnf M1 N1.
unify_whnf M N :- M = N, !.
unify_whnf (succ M) (succ N) :- unify M N.
unify_whnf (eq A X Y) (eq A1 X1 Y1) :- unify A A1, unify X X1, unify Y Y1.
unify_whnf (prod A F) (prod B G) :- unify A B, pi x\ unify (F x) (G x).
unify_whnf (app M N) (app M1 N1) :- unify_whnf M M1, unify N N1.
```

`build`의 `im` 줄에서 `H`가 암시적 인자의 hole이다. clause의 새 변수이므로 따로 만들 필요가 없다.

### A.4 디버깅 모드에서 항 건설 (2.4절)

A.3에 더한 것이다. 두 clause는 `elabc`의 다른 clause보다 앞에 둔다.

```
type runder raw.
type rlam ((tm -> raw) -> raw).
type reflc tm.

elabc runder T M :- !, debug "goal", elabc R T M.
elabc (rlam F) T (lam A M) :- !, whnf T (prod A B), pi x\ of x A => elabc (F x) (B x) (M x).

typeof reflc (prod (typ 0) (a\ prod a (x\ eq a x x))).
implicits reflc (im :: im :: []).
```

`R`을 할당하지 않고 진행하면 `elabc ?R T M`이 첫 clause와 다시 맞아 `debug`를 또 부른다. 그래서 답하지 않은 목표는 다시 물어 온다.

세션의 입력(BETA 인터프리터, `Hol --test`):

```
?- elabc runder (prod nat_ty (n\ eq nat_ty (app (app add zero) n) n)) M.
:assign ?V_2230 := rlam (n\ runder).
:d
:assign ?V_2302 := rhd reflc.
:d
```

`:d`는 디버깅을 끄고 다음 `debug`까지 진행시킨다. 변수 이름은 화면에 표시된 것을 읽어 쓴 것이다.

## 부록 B. 참고

- The Rocq Prover Reference Manual, "Core language" (sorts, 변환 규칙, 귀납형과 재귀 함수).
- C. Dunchev, F. Guidi, C. Sacerdoti Coen, E. Tassi. ELPI: fast, Embeddable, λProlog Interpreter. LPAR-20, 2015.
- F. Guidi, C. Sacerdoti Coen, E. Tassi. Implementing type theory in higher order constraint logic programming. Mathematical Structures in Computer Science 29(8), 2019. ELPI로 CIC의 검사기와 refiner를 구현하고 mode와 제약이 왜 필요한지를 다룬다.
- A. Asperti, W. Ricciotti, C. Sacerdoti Coen, E. Tassi. A compact kernel for the calculus of inductive constructions. Sadhana 34(1), 2009.
- A. Asperti, W. Ricciotti, C. Sacerdoti Coen, E. Tassi. A bi-directional refinement algorithm for the calculus of (co)inductive constructions. Logical Methods in Computer Science 8(1), 2012.
- M. Sozeau, S. Boulier, Y. Forster, N. Tabareau, T. Winterhalter. Coq Coq Correct! Verification of type checking and erasure for Coq, in Coq. POPL 2020.
- E. Giménez. Codifying guarded definitions with recursive schemes. TYPES 1994.
- A. J. C. Hurkens. A simplification of Girard's paradox. TLCA 1995.
- D. Miller. A logic programming language with lambda-abstraction, function variables, and simple unification. Journal of Logic and Computation 1(4), 1991.
- M. Carneiro. The type theory of Lean. 2019.

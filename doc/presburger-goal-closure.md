# Presburger 목표의 자유변수 닫음과 잔여제약

이 문서는 `presburger "phi"` 목표(goal)가 자유변수를 어떻게 양화(quantify)해
판정하는지에 대한 설계 기록이다. 1단계(lia식 닫음)는 구현 완료, 2단계(잔여제약
도입)는 계획 상태다. 관련 코드는 `Hol.BETA.Arith`, `Hol.BETA.Runtime`,
`Hol.BETA.Main` 이다.

## 1. 배경 — 무엇이 틀렸나

`presburger "phi"` 리터럴은 `NPresburgerCheck rep freeOf` 노드로 desugar되고,
`freeOf :: Map MyVar TermNode` 가 문자열 안의 자유 이름(예: `X`)을 같은 철자의
바깥 HOL 변수에 연결한다(`outer_var.hol`). 런타임은 `runPresburger` 에서 이
formula를 판정한다.

기존 구현은 `entails` 가 남은 자유변수를 전부 **전칭(∀)** 으로 닫았고
(`foldr AllF body fvs`), 예외로 `isLocalWitness` 가 **벌거벗은 `LVar (LV_Unique _)`**
만 존칭(∃)으로 처리했다. 이 방식에는 두 결함이 있었다.

- **불완전(incomplete).** 구성자 아래 들어간 논리변수(`s X`)나 `LV_Named` 쿼리
  변수는 `isLocalWitness` 에 안 걸려 ∀로 닫혔다. 그래서
  `?- p (s X).` (단, `p X :- presburger "exists Y, X + Y = 6"`)가 `∀X. ∃Y. (X+1)+Y=6`
  → `no` 였다. 해가 존재하므로(X=0..5) `yes` 여야 한다.
- **불건전(unsound).** 양화 순서가 항상 "∀ 바깥 / ∃ 안쪽"으로 고정돼 있었다.
  그래서 `?- sigma X\ pi C\ presburger "X = C".` 가 참값 `∃X. ∀C. X=C`(거짓,
  `no`)인데도 `∀C. ∃X. X=C`(참)로 뒤집혀 `yes` 를 냈다.

핵심 원인: 양화를 **변수의 정체(논리변수냐 eigenvariable이냐)** 와 **도입
순서(scope)** 가 아니라, **항의 구문적 모양**으로 결정했다는 것.

## 2. 올바른 의미론

`presburger phi` 의 각 자유 원자는 증명 상태에서 셋 중 하나이며, 그에 따라
양화된다.

| 원자 | 출처 | 양화 |
| -- | -- | -- |
| 논리변수 `LVar` | `sigma`, top-level 쿼리, clause 인스턴스화 | ∃ (해를 찾는 대상) |
| eigenvariable `NCon (DC_Unique …)` | `pi` | ∀ (임의의 고정값) |
| 닫힌 nat | — | 상수로 fold |
| 분해 불가한 비산술 항 | freeOf 치환 결과 | ∀ (uninterpreted로 간주, 건전·불완전) |

양화 prefix의 **순서는 도입 순서(scope 중첩)** 를 따른다. 도입 순서는 fresh
`Unique` 의 생성 순서와 같으므로, `unUnique` 오름차순 = outermost 가 유효한
prenex 선형화다. 예:

- `sigma X\ pi C\ presburger "X = C"` → X(먼저)=∃ 바깥, C(나중)=∀ 안쪽 →
  `∃X. ∀C. X=C` → `no`
- `pi C\ sigma X\ presburger "X = C"` → C(먼저)=∀ 바깥, X(나중)=∃ 안쪽 →
  `∀C. ∃X. X=C` → `yes`

opaque 비산술 항(`f X` 등)을 ∀로 두는 것은 lia(Coq)의 전략과 같다: uninterpreted
한 덩어리는 "모든 값에 대해 성립"해야 통과시킨다. 건전하지만 불완전하다. ∃로
두면 불건전해진다(예: `f` 가 상수함수 0이면 `∃X. f X > 5` 는 거짓인데 `∃Z. Z>5`
는 참).

## 3. 1단계 — lia식 닫음 (구현 완료)

`runPresburger` 가 `Hol.BETA.Arith.presburgerGoalHolds` 를 호출한다. 동작:

1. **분해.** 각 자유항을 `0`/`s`/`+`/상수배로 분해해 leaf를 드러낸다
   (`leafTerm`). `s X` 는 `Succ (IVar v_X)` 가 되고 안쪽 X가 노출된다.
2. **atomize.** 분해 불가한 leaf만 fresh 변수 하나로 묶는다. 같은 항은 같은
   변수를 재사용한다(`internAtom` 의 `leafInverse`).
3. **분류.** leaf가 `LVar` 이면 ∃, `DC_Unique`(eigenvariable)이면 ∀, opaque면
   ∀ (`lvOrderKey`/`opaqueOrderKey` 가 도입 순서 키도 함께 부여).
4. **prenex.** leaf들을 도입 순서 키로 정렬해 ∃/∀ 를 바깥→안쪽으로 쌓는다.
   문자열 자신의 `exists`/`forall` 바운드 변수는 그대로 둔다.
5. **body.** `(∧ hyps) ∧ phi`. hyps 는 문맥의 deferred `ArithmeticConstraint`
   들이다(현재는 비교연산자 경로가 남긴 것).
6. **판정.** `eliminateQuantifierReferringToTheBookWrittenByPeterHinman` 후
   `checkTruthValueOfMyPresburgerFormula == Just True`.

`entails` / `isInconsistent` / `arithEntails` 는 다른 경로라 이 단계에서 건드리지
않았다.

### 검증

- `?- p (s X).` → `yes` (이전 `no`)
- `?- sigma X\ p (s X).` → `yes` / `?- pi X\ p (s X).` → `no`
- `?- sigma X\ pi C\ presburger "X = C".` → `no` (이전 불건전 `yes`)
- `?- pi C\ sigma X\ presburger "X = C".` → `yes`

회귀 가드: `test/presburger/quantifier_order.hol` (기대 yes/no/no/yes).

## 4. 2a단계 — 잔여제약(deferral) 도입 (구현 완료)

### 동기

1단계는 `presburger phi` 를 **일회성 판정**으로 쓰고 phi를 폐기했다. 그래서
여러 presburger 체크가 retention 없이 같은 자유변수를 공유하면 불건전해졌다.
예: `?- presburger "X > 10", presburger "X < 8".` 는 각 체크가 이전 phi를 못 봐서
독립적으로 통과해 `yes` 였으나, 실제로는 `X>10 ∧ X<8` 이 불충족이다.

해법은 비교연산자 경로처럼 **phi를 잔여제약으로 retain** 하는 것이다. 즉
`presburger phi` 는 "store ∧ phi 가 **충족가능**하면 성공하고 phi를 retain" 한다.
이 충족가능성 판정이 바로 lia 엔진(`presburgerStoreSat`)이 계산하는 것이므로,
lia 클로저가 그대로 **defer의 일관성 오라클**이 된다.

### 구현

`closeStore`/`presburgerStoreSat`(`Hol.BETA.Arith`)를 **리스트 기반**으로
일반화했다: 비교 hypotheses(`TermNode`)와 presburger 제약(`(rep, freeOf)`)을
**하나의 공유 leaf 환경**에서 atomize·양화해 한 prenex로 닫는다(공유 변수는 한
번만 양화). 손본 곳:

1. **store 종류.** `Constraint` 에 `PresburgerConstraint rep freeOf` 추가
   (`Hol.BETA.Runtime`). 비교제약과 달리 formula라 단일 TermNode로는 부족하다.
2. **gate.** `runPresburger` 는 phi를 store에 넣고 `storeSatisfiable ctx'`
   (= `presburgerStoreSat` 로 전체 store 판정)이 참일 때만 성공. `arithOpCheck` 도
   presburger 제약이 있으면 전체 store를 함께 검사(비교제약을 retained
   presburger와 교차 검증).
3. **zonk.** `zonkLVar (PresburgerConstraint rep freeOf)` 가 freeOf 항을 재작성
   (`NPresburgerCheck` 의 rewrite와 같은 원리).
4. **리포팅.** `Show Constraint` 가 `NPresburgerCheck` 렌더(`renderPresburger`)를
   재사용해 `presburger "..."` 로 출력.
5. **드롭(`groundDropped`).** 잔여 presburger 제약을 다음 두 경우에 버린다:
   `presburgerValid`(보편타당 — 정보 없음, 예 `p 6`/`pi X\ "X=X"`), 또는 탈출하는
   (LV_Named) 자유변수가 없고(=로컬) 단독 충족가능(탐색 중 이미 해소됨, 예
   `sigma X\ p (s X)`). `contradicts` 는 단독 불충족 presburger 제약을 잡는다.

비교제약의 `TermNode` 저장·렌더는 **그대로 두었다.** 모든 기존 byte-exact
테스트가 유지된다(`presburger_view.hol` 만 retained 제약이 `_constraints` 디버그
뷰에 나타나도록 재베이스라인). 덤으로 `isInconsistent` 의 ∀-only 한계가 닿던
경로(presburger 포함 store)는 이제 올바른 ∃/∀/순서 판정으로 검사된다.

검증:

- `?- presburger "X > 10", presburger "X < 8".` → `no` (이전 불건전 `yes`)
- `?- presburger "X = 5", X > 7.` → `no` (비교제약이 retained presburger를 죽임)
- `?- presburger "X = 5", X > 3.` → `yes`, 잔여 `X > 3` / `presburger "X = 5"` 보고
- `?- p 6.` → `yes` 깨끗 / `?- sigma X\ p (s X).` → `yes` 깨끗(로컬 드롭)

회귀 가드: `test/presburger/residual_presburger.hol`. 전체 smoke 71/71.

### 2b단계 — 완전 통일 (후속, 미구현)

저장·렌더 이중성까지 흡수(비교제약도 formula로 통일). 이때
`residual.hol`/`entailment_drop.hol` 을 의도적으로 재베이스라인하고, entailment
기반 드롭을 formula 레벨 `entails` 로 일반화한다.

## 5. 트레이드오프와 한계

- **opaque 비산술 항** 은 ∀로 둔다(건전, 불완전). `presburger "f X > 5"` 류는
  충족가능성 판정에서 보수적으로 다뤄진다.
- **QE 성능.** 양화 formula를 store에 달고 다니며 conjunction을 재판정하면
  Presburger QE(지수급) 부담이 누적된다. 전체 store 판정은 "presburger 제약이
  실제로 존재할 때"로 한정하고(`hasPresburgerConstraint` 가드), 비교제약만 있는
  hot path는 기존 `isInconsistent` 만 쓰도록 두었다.
- **리포팅(미세).** 쿼리변수가 clause 변수에 묶여 제약이 그 로컬 변수를 참조하면
  (`?- p (s X).`), 제약이 "로컬 + 충족가능"으로 드롭되고 답 치환 `X := ?V_…` 만
  보인다(1단계와 동일). 제약이 탈출 변수를 직접 참조할 때만(`presburger "X = 5"`)
  잔여로 표시된다. presburger 제약은 바인딩을 posting하지 않으므로 `X = 5` 같은
  결정적 제약도 풀어서 `X := 5` 로 보이지 않고 잔여로 남는다.
- **로컬 드롭의 건전성.** 로컬(비탈출) 제약은 "단독 충족가능"일 때만 드롭한다.
  탐색 중 전체 store가 충족가능으로 게이트됐으므로 성공 시점에 로컬 존재는 공동
  해소 가능 → 드롭 안전. 단독 불충족이면 `contradicts` 가 잡는다.

## 6. 코드 위치

- `Hol.BETA.Arith` — `closeStore`/`presburgerStoreSat`(store 충족가능성, lia식
  닫음), `presburgerValid`(잔여 드롭용 보편타당성), `renumFormulaDecomp`/
  `renumTermDecomp`/`leafTerm`/`internAtom`/`leafFormula`/`lvOrderKey`/
  `opaqueOrderKey`.
- `Hol.BETA.Runtime` — `Constraint` 의 `PresburgerConstraint`, `runPresburger`
  (retain+gate), `storeSatisfiable`/`hasPresburgerConstraint`, `arithOpCheck`
  (교차 검사), `zonkLVar`/`Show Constraint` 의 presburger 케이스.
- `Hol.BETA.Main` — `groundDropped`(presburger 드롭: `presburgerValid` 또는
  로컬+충족) / `contradicts`(단독 불충족) / `hasNamedFreeVar`.
- 테스트: `test/presburger/{quantifier_order,residual_presburger,outer_var,
  quantified,solver_sanity,basic,consistency,residual,entailment_drop}.hol`,
  `test/debug/presburger_view.hol`.

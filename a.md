# Project A

## Forethought

### Question
Coq 퍼징 테스트를 Koen Claessen식으로 접근하고 싶습니다.
Coq 퍼징 테스트 목표는 [gofile.go 가 임의로 주어질 때 gofile.go를 Go compiler로 돌려서 바이너리를 실행해 얻는 외부에서 observable한 behavior와
```
gofile.go --[ my translator ]-> gofile.v (itree semantics) --[ Coq->Haskell extraction ]-> gofile.hs
```
의 패스로 얻은 gofile.hs의 외부에서 observable한 behavior가 같아야 한다]는 것을 검증하는 것입니다.
gofile.v를 매번 생성하고 coqc 컴파일하고 extraction하여 비교하는 방식으로 진행하고 싶은데, 전체 plan을 그려주세요.

### Answer
좋습니다. 이 경우에는 **“Coq 안에서 property를 증명한다”가 아니라, Coq를 거치는 컴파일/추출 파이프라인 전체를 하나의 피실험 컴파일러로 보고 differential fuzzing** 하는 것이 맞습니다.

핵심 property는 다음입니다.

```text
obs(run(go build gofile.go))
=
obs(run(ghc gofile.hs))
```

여기서 `gofile.hs`는

```text
gofile.go
  -- translator -->
gofile.v
  -- coqc -->
extracted Haskell
  -- ghc/runhaskell -->
observable behavior
```

로 얻습니다.

QuickCheck의 원래 정신은 “property를 Haskell 함수로 쓰고, random input을 생성하고, 실패 시 counterexample을 줄인다”는 것입니다. Claessen/Hughes의 QuickCheck도 명시적으로 property-based random testing을 목표로 합니다. ([ACM Digital Library][1]) 여기에 Koen Claessen식 “Bool 대신 연속적인 score/objective를 두고 counterexample을 향해 search/minimize한다”는 아이디어를 얹으면 됩니다.

---

# 1. 전체 아키텍처

큰 그림은 이렇게 잡으면 됩니다.

```text
                    ┌────────────────────┐
                    │  Program Generator │
                    │  Go AST + inputs   │
                    └─────────┬──────────┘
                              │
                              v
                       test-N/gofile.go
                              │
          ┌───────────────────┴───────────────────┐
          │                                       │
          v                                       v
   Native Go oracle                      Coq extraction path
          │                                       │
          v                                       v
   go build / go run                  translator: gofile.go -> gofile.v
          │                                       │
          v                                       v
   native executable                    coqc gofile.v
          │                                       │
          v                                       v
   run with stdin/args/env              extraction: gofile.hs
          │                                       │
          v                                       v
   obs_go                              ghc / runhaskell gofile.hs
          │                                       │
          └───────────────────┬───────────────────┘
                              v
                     compare observations
                              │
              ┌───────────────┴───────────────┐
              │                               │
              v                               v
          pass/cache                    fail + shrink/minimize
```

테스트 하나는 다음 디렉토리 단위로 관리하는 것이 좋습니다.

```text
cases/
  000001/
    seed.json
    gofile.go
    input.stdin
    args.txt
    env.json
    native/
      build.log
      stdout.bin
      stderr.bin
      exit.code
      timeout
    coq/
      gofile.v
      coqc.log
      extracted/
        Gofile.hs
        Runtime.hs
      ghc.log
      stdout.bin
      stderr.bin
      exit.code
      timeout
    result.json
```

이렇게 해야 실패 케이스가 나왔을 때 재현성이 생깁니다.

---

# 2. 먼저 observable behavior를 엄격히 정의해야 합니다

가장 먼저 해야 할 일은 “같다”의 의미를 정하는 것입니다.

추천하는 관찰값은 다음입니다.

```hs
data Obs = Obs
  { exitCode :: ExitCodeLike
  , stdout   :: ByteString
  , stderr   :: Maybe ByteString
  , timedOut :: Bool
  , signal   :: Maybe Signal
  }
```

초기에는 `stderr`는 비교 대상에서 빼는 편이 좋습니다. Go compiler/runtime과 Haskell runtime의 에러 메시지가 다를 수 있기 때문입니다.

즉, 1차 버전은 다음 정도가 적절합니다.

```text
observable behavior =
  (termination class, exit code, stdout bytes)
```

termination class는 다음처럼 나눕니다.

```text
Terminated exit-code
TimedOut
CompileError
TranslatorError
CoqError
ExtractionError
HaskellCompileError
RuntimePanic
```

하지만 중요한 점이 있습니다.

**Go compiler가 reject한 프로그램은 일반 equivalence test 대상에서 제외해야 합니다.** 즉 generator가 만든 `gofile.go`가 Go compiler에서 typecheck/build 실패하면 그것은 “invalid test input”이지 translator bug가 아닙니다.

반대로, Go compiler는 accept했는데 translator/coqc/extraction/ghc가 실패하면 그것은 매우 좋은 counterexample입니다.

---

# 3. 테스트 property를 Haskell에서 이렇게 잡습니다

기본 property는 Boolean으로는 이렇게 생깁니다.

```hs
prop_go_coq_extraction_equiv :: TestCase -> IO PropertyResult
prop_go_coq_extraction_equiv tc = do
  obsGo <- runNativeGo tc
  case obsGo of
    InvalidGoProgram -> pure Discard
    ValidGo obs1 -> do
      obsHs <- runCoqExtractionPath tc
      pure $
        if comparable obs1 obsHs && obs1 == obsHs
        then Pass
        else Fail obs1 obsHs
```

그러나 Koen Claessen식으로 가려면 이걸 곧장 `Bool`로 끝내지 말고, 다음처럼 **failure를 향한 objective**를 둡니다.

```hs
score :: TestCase -> IO Score
```

여기서 목표는 다음입니다.

```text
score = 0      means counterexample found
score = small  means suspicious / near miss
score = large  means boring passing case
score = ∞      means invalid / irrelevant case
```

중요한 방향은 property 자체가 아니라 **property violation**을 target으로 삼는 것입니다.

```text
target(gofile.go) = "Go path와 Coq-extraction path가 다르다"
```

그러면

```text
target true  = 0
target false = positive distance
invalid      = ∞
```

로 둘 수 있습니다.

---

# 4. 1단계는 반드시 boring한 differential fuzzer로 시작하세요

처음부터 수치 objective minimization을 넣으면 디버깅이 어려워집니다. 추천 순서는 다음입니다.

## Phase A. Deterministic end-to-end runner

먼저 하나의 seed에 대해 다음 명령을 안정적으로 수행하는 runner를 만듭니다.

```bash
fuzz-one --seed 12345
```

내부적으로는 다음을 합니다.

```text
1. seed에서 Go program 생성
2. gofmt
3. go build 또는 go run으로 native oracle 실행
4. translator 실행: gofile.go -> gofile.v
5. coqc gofile.v
6. extraction 결과 Haskell 파일 확인
7. ghc 또는 runhaskell 실행
8. stdout/exit code 비교
9. result.json 저장
```

이 단계에서는 QuickCheck도 필요 없습니다. 그냥 seed 하나를 재현 가능하게 돌리는 것이 먼저입니다.

---

## Phase B. QuickCheck/Hedgehog style random testing

그다음 Haskell 쪽에 generator를 둡니다.

```hs
data TestCase = TestCase
  { tcSeed  :: Seed
  , tcProg  :: GoProgram
  , tcInput :: RuntimeInput
  }
```

그리고 property를 돌립니다.

```hs
prop_equiv :: TestCase -> Property
```

실패하면 `TestCase` 전체를 저장합니다.

QuickCheck은 random input generation과 counterexample shrinking이 핵심이고, 실패한 입력을 더 작게 줄여주는 것이 매우 중요합니다. ([위키백과][2])

이 단계에서는 목표가 단순합니다.

```text
많이 만들고,
둘 다 실행하고,
다르면 저장한다.
```

---

# 5. Go generator는 처음부터 전체 Go를 만들면 안 됩니다

처음 generator는 아주 작은 Go subset에서 시작해야 합니다.

추천 subset v0:

```go
package main

func main() {
    var x int = ...
    var y int = ...
    fmt.Println(expr)
}
```

지원할 것:

```text
types:
  int, bool, string

expressions:
  literals
  variables
  +, -, *, /, %
  ==, !=, <, <=, >, >=
  &&, ||, !
  if expression은 Go에 없으므로 statement로 처리

statements:
  var declaration
  assignment
  if
  for with bounded loop
  fmt.Println
```

처음에는 제외할 것:

```text
goroutine
channel
map iteration order
reflection
unsafe
floating point
panic/recover
defer
interfaces
method set
package import complexity
nondeterminism
time/random/os
```

특히 `map` iteration, goroutine scheduling, time, filesystem, network는 observable behavior가 비결정적이므로 초기 fuzzing에서 빼야 합니다.

---

# 6. generator는 “typed AST generator”로 만드세요

문자열을 랜덤으로 찍어서 Go parser에게 맡기는 방식은 비효율적입니다.

대신 Haskell에서 typed AST를 만듭니다.

```hs
data Ty
  = TInt
  | TBool
  | TString

data Expr ty where
  EInt    :: Int -> Expr TInt
  EBool   :: Bool -> Expr TBool
  EString :: String -> Expr TString
  EVar    :: Var ty -> Expr ty
  EAdd    :: Expr TInt -> Expr TInt -> Expr TInt
  ELt     :: Expr TInt -> Expr TInt -> Expr TBool
  EEqInt  :: Expr TInt -> Expr TInt -> Expr TBool
  ENot    :: Expr TBool -> Expr TBool
  EAnd    :: Expr TBool -> Expr TBool -> Expr TBool
```

statement도 environment를 들고 생성합니다.

```hs
genStmt :: Env -> Size -> Gen (Stmt, Env)
genExpr :: Env -> Ty -> Size -> Gen (Expr ty)
```

이렇게 하면 Go compiler reject 비율이 크게 줄어듭니다.

---

# 7. extraction path는 매번 새로 하지 말고 계층화하세요

매 테스트마다 `coqc`와 `ghc`를 전부 돌리면 매우 느립니다. 그래도 사용자가 말한 방식처럼 “매번 gofile.v 생성, coqc 컴파일, extraction”을 하려면 다음처럼 나눠야 합니다.

## 고정 부분

```text
Runtime.v
GoSemantics.v
IreeInterpreter.v
ExtractionSetup.v
```

이것들은 한 번만 컴파일합니다.

```bash
coqc Runtime.v
coqc GoSemantics.v
coqc ExtractionSetup.v
```

## 테스트마다 바뀌는 부분

```text
Generated/gofile_000123.v
```

내용은 대략 다음처럼 합니다.

```coq
From MyProject Require Import Runtime GoSemantics ExtractionSetup.

Definition prog : GoProgram := ... translated AST ...

Definition main_itree : itree Eff unit :=
  denote_program prog.

Extraction "extracted/Gofile_000123.hs" main_itree.
```

그런 다음 테스트마다:

```bash
coqc -Q theories MyProject Generated/gofile_000123.v
ghc extracted/Gofile_000123.hs runtime_hs/*.hs -o case.exe
```

로 갑니다.

---

# 8. Haskell extraction 결과는 “실행 가능한 main”으로 감싸야 합니다

Coq extraction 결과가 보통 순수 함수나 itree interpreter 형태일 것이므로, 다음을 고정 runtime으로 둡니다.

```hs
module Main where

import ExtractedGofile
import Runtime.Driver

main :: IO ()
main = runGoMain extracted_main
```

즉 매번 extraction된 코드만 바뀌고, driver는 고정합니다.

```text
Extracted program: semantics value
Fixed Haskell runtime: IO로 observable behavior 생성
```

비교 대상은 Go native binary와 이 Haskell driver의 실행 결과입니다.

---

# 9. timeout은 반드시 넣으세요

각 단계에 timeout이 있어야 합니다.

예:

```text
go build: 2s
native run: 1s
translator: 2s
coqc: 5s
ghc: 5s
haskell run: 1s
```

특히 generated Go program에 loop가 있으면 native Go와 extracted Haskell이 둘 다 발산할 수 있습니다. 발산 equivalence를 완벽히 테스트할 수 없으므로 초기에는 bounded loop만 생성하세요.

예를 들어 generator가

```go
for i := 0; i < n; i++ {
   ...
}
```

꼴만 만들고 `n`을 작은 상수로 제한합니다.

---

# 10. 실패 분류를 잘 해야 합니다

모든 실패를 같은 것으로 보면 안 됩니다.

추천 classification:

```text
A. Go rejected
   -> discard

B. Go accepted, translator failed
   -> translator completeness bug

C. Go accepted, translator succeeded, coqc failed
   -> generated Coq ill-typed
   -> translator soundness/type preservation bug

D. coqc succeeded, extraction failed
   -> extraction setup bug

E. extraction succeeded, ghc failed
   -> extraction/runtime Haskell integration bug

F. both ran, obs differ
   -> semantic mismatch bug

G. native timeout, extracted timeout
   -> probably inconclusive/pass depending on policy

H. native terminates, extracted timeout
   -> semantic mismatch

I. native timeout, extracted terminates
   -> semantic mismatch or timeout threshold issue
```

가장 중요한 버그는 C와 F입니다.

```text
C: translator가 Coq term을 잘못 생성함
F: semantics가 Go와 다름
```

---

# 11. shrinking 전략

실패한 `gofile.go`를 줄이는 것이 핵심입니다.

AST-level shrinker를 둡니다.

예:

```text
Program shrink:
  remove function
  remove statement
  replace block by sub-block
  inline temporary variable
  replace expression by subexpression
  replace constant by 0, 1, -1, small number
  replace string by "", "a"
  replace if condition by true/false
  remove else branch
  reduce loop bound
```

예를 들어 실패 프로그램이

```go
var x int = ((a + 0) * 1)
fmt.Println(x)
```

이면 shrinker가

```go
fmt.Println(a)
```

까지 줄일 수 있어야 합니다.

이때 shrinker는 Go source string이 아니라 AST에서 작동해야 합니다.

---

# 12. Koen Claessen식 objective minimization은 어디에 들어가나?

일반 QuickCheck식은 다음입니다.

```text
random generate -> bool property check -> fail이면 shrink
```

Claessen식으로 더 가면 다음이 됩니다.

```text
random/search generate -> quantitative objective 계산 -> objective가 작아지는 방향으로 mutate/minimize
```

여기서 objective는 “counterexample에 가까운 정도”입니다.

당장 쓸 수 있는 objective는 다음처럼 정의할 수 있습니다.

```hs
data Score
  = FoundCounterexample Failure
  | Score Double
  | Irrelevant
```

비교 함수는 다음입니다.

```hs
scoreCase :: TestCase -> IO Score
scoreCase tc = do
  r <- runPipeline tc
  pure $ case r of
    InvalidGo ->
      Irrelevant

    TranslatorFailed ->
      FoundCounterexample TranslatorCrash

    CoqFailed ->
      FoundCounterexample IllTypedCoq

    HaskellCompileFailed ->
      FoundCounterexample BadExtraction

    Ran obsGo obsHs
      | obsGo /= obsHs ->
          FoundCounterexample (ObsMismatch obsGo obsHs)
      | otherwise ->
          Score (interestingness tc obsGo obsHs)
```

여기서 `interestingness`를 잘 설계해야 합니다.

초기 버전은 다음 정도면 됩니다.

```hs
interestingness :: TestCase -> Obs -> Obs -> Double
interestingness tc obsGo obsHs =
    branchDistance tc
  + coveragePenalty tc
  + simplicityPenalty tc
```

하지만 주의할 점이 있습니다.

`obsGo == obsHs`인 경우에는 아직 bug가 없으므로, objective는 “이 프로그램이 얼마나 bug를 만들 법한가?”를 나타내야 합니다.

추천 feature:

```text
1. 새로운 translator branch를 많이 타는가?
2. 새로운 Coq constructor를 생성하는가?
3. zero initialization, struct, array, pointer 등 위험 feature를 포함하는가?
4. native output과 extracted output이 숫자상 가까이 달라질 뻔했는가?
5. timeout에 가까운가?
6. panic/error boundary에 가까운가?
```

---

# 13. 구체적인 score 예시

예를 들어 integer expression mismatch를 노린다면 다음처럼 할 수 있습니다.

```hs
distanceOutput :: Obs -> Obs -> Double
distanceOutput obsGo obsHs =
  case (parseInt (stdout obsGo), parseInt (stdout obsHs)) of
    (Just x, Just y) ->
      if x == y then 10 else 0
    _ ->
      if stdout obsGo == stdout obsHs then 10 else 0
```

하지만 이것은 mismatch가 이미 나와야 0입니다.

더 Claessen식으로 하려면 generator 내부 expression에 objective를 전파합니다.

예를 들어 division bug를 의심한다면:

```text
x / y에서 y가 0에 가까울수록 score를 낮춤
x % y에서 negative operand가 나올수록 score를 낮춤
overflow boundary에 가까울수록 score를 낮춤
```

즉:

```hs
riskExpr :: Expr ty -> Double
riskExpr expr =
  minimum
    [ distanceToZeroDivisor expr
    , distanceToNegativeModulo expr
    , distanceToOverflow expr
    , distanceToShortCircuitBoundary expr
    ]
```

그리고 전체 score:

```hs
interestingness tc obsGo obsHs =
  min
    (riskExprs tc)
    (coverageNoveltyPenalty tc)
```

목표는 `interestingness`를 minimize하는 것입니다.

---

# 14. search loop

최종 fuzzing loop는 다음처럼 됩니다.

```text
1. seed에서 TestCase 생성
2. pipeline 실행
3. counterexample이면 저장 후 shrink
4. 아니면 score 계산
5. score가 좋은 case는 corpus에 저장
6. corpus에서 case를 골라 mutate
7. 다시 반복
```

의사코드:

```hs
loop :: Corpus -> IO ()
loop corpus = do
  parent <- choose corpus
  child  <- mutateOrGenerate parent
  score  <- scoreCase child

  case score of
    FoundCounterexample fail -> do
      small <- shrinkCase child
      saveFailure small fail
      loop corpus

    Irrelevant ->
      loop corpus

    Score d -> do
      let corpus' =
            if isInteresting d child corpus
            then insert child d corpus
            else corpus
      loop corpus'
```

이 구조가 단순 random QuickCheck보다 좋습니다. 왜냐하면 “좋았던 test case 주변”을 계속 파기 때문입니다.

---

# 15. corpus를 feature coverage 기준으로 관리하세요

coverage-guided fuzzing처럼 corpus를 유지하는 것이 좋습니다.

각 generated Go program에서 feature vector를 뽑습니다.

```hs
data Feature
  = UsesArray
  | UsesStruct
  | UsesPointer
  | UsesShortCircuit
  | UsesNestedIf
  | UsesForLoop
  | UsesZeroInit
  | UsesCompositeLiteral
  | UsesFunctionCall
  | UsesMultipleReturn
  | UsesShadowing
  | UsesNamedType
```

그리고 translator가 생성한 Coq 쪽에서도 feature를 뽑을 수 있으면 더 좋습니다.

```text
Generated Coq contains:
  assign_zero_value
  denote_expr_binop
  denote_stmt_for
  denote_call
  memory_load
  memory_store
```

corpus 저장 기준:

```text
- 새로운 feature 조합을 만들었다
- 기존 feature보다 작은 프로그램이다
- score가 더 낮다
- 특정 failure boundary에 가까워졌다
```

---

# 16. Coq compilation 비용을 줄이는 현실적인 최적화

매번 `coqc + extraction + ghc`를 하면 매우 느립니다. 그래도 이 방식을 유지하려면 다음 최적화가 필요합니다.

## 16.1 `.vo` cache

고정 라이브러리는 미리 컴파일합니다.

```bash
make theories
```

테스트마다 generated file만 컴파일합니다.

```bash
coqc -Q theories MyProject _build/case_123/Gofile.v
```

## 16.2 extraction runtime 고정

매번 runtime까지 extraction하지 말고, generated program 부분만 extraction합니다.

## 16.3 GHC 대신 runghc와 compiled driver 비교

초기에는 `runghc`가 편하지만 느릴 수 있습니다. 안정화되면 다음 구조가 낫습니다.

```text
fixed Runtime compiled once
generated ExtractedProgram compiled per case
```

## 16.4 parallel execution

테스트 케이스끼리는 독립적이므로 N개 worker로 나눕니다.

```bash
fuzz --jobs 16
```

## 16.5 hash cache

같은 AST가 다시 나오면 재실행하지 않습니다.

```text
hash(gofile.go, input, translator version, Coq version, runtime version)
```

를 key로 result를 cache합니다.

---

# 17. CI에서는 두 종류로 나누세요

## 빠른 smoke fuzz

매 PR마다:

```text
100~500 cases
small size
no expensive features
timeout short
```

## nightly fuzz

매일 밤:

```text
10,000~100,000 cases
larger size
more features
parallel
corpus-based mutation
```

## regression fuzz

발견된 실패는 반드시 `regressions/`에 고정합니다.

```text
regressions/
  issue-001-zero-init-array/
    gofile.go
    input.stdin
    expected.json
  issue-002-short-circuit-side-effect/
    gofile.go
    input.stdin
    expected.json
```

이건 fuzzing과 별개로 항상 돌려야 합니다.

---

# 18. 가장 먼저 노릴 feature 순서

제 생각에는 이 순서가 좋습니다.

```text
0. int/bool/string expression
1. if / block / variable shadowing
2. short-circuit: &&, ||
3. zero initialization
4. arrays
5. structs
6. function calls
7. multiple return
8. pointers
9. slices
10. methods/interfaces
11. panic/defer/recover
12. goroutines/channels
```

지금 프로젝트 맥락상 특히 먼저 노릴 것은 이것입니다.

```text
zero initialization
array/struct initialization
assignment
function call
short-circuit evaluation
```

왜냐하면 이 부분들은 Coq semantics와 Go compiler behavior가 어긋나기 쉽고, translator가 생성하는 Coq term도 복잡해지기 때문입니다.

---

# 19. 추천 구현 모듈 구조

Haskell fuzzer 쪽은 대략 이렇게 나누면 좋습니다.

```text
fuzzer/
  app/
    Main.hs

  src/
    Go/AST.hs
    Go/Pretty.hs
    Go/Gen.hs
    Go/Shrink.hs
    Go/Feature.hs

    Pipeline/NativeGo.hs
    Pipeline/Translator.hs
    Pipeline/Coq.hs
    Pipeline/Extraction.hs
    Pipeline/HaskellRun.hs
    Pipeline/Observe.hs

    Fuzz/Score.hs
    Fuzz/Corpus.hs
    Fuzz/Mutate.hs
    Fuzz/Loop.hs
    Fuzz/Shrink.hs

    Util/Process.hs
    Util/Timeout.hs
    Util/Hash.hs
```

핵심 타입은 다음 정도입니다.

```hs
data TestCase = TestCase
  { tcProgram :: GoProgram
  , tcInput   :: RuntimeInput
  , tcSeed    :: Int
  }

data PipelineResult
  = InvalidGo CompileLog
  | TranslatorError Log
  | CoqError Log
  | ExtractionError Log
  | HaskellCompileError Log
  | RanBoth Obs Obs

data Failure
  = TranslatorCompletenessBug
  | IllTypedGeneratedCoq
  | BadExtraction
  | ObservableMismatch Obs Obs
  | TerminationMismatch Obs Obs
```

---

# 20. 최종 plan 요약

제가 추천하는 전체 plan은 다음입니다.

```text
Step 1.
  observable behavior를 정의한다.
  우선 stdout bytes + exit code + timeout만 비교한다.

Step 2.
  seed 하나를 받아 gofile.go를 만들고,
  native Go path와 Coq-extraction-Haskell path를 모두 실행하는
  deterministic runner를 만든다.

Step 3.
  작은 typed Go subset generator를 만든다.
  처음에는 int/bool/string, var, assignment, if, bounded for, fmt.Println만 지원한다.

Step 4.
  Boolean differential property를 만든다.
  Go accepted인데 translator/coqc/ghc/run 결과가 실패하거나 obs가 다르면 counterexample이다.

Step 5.
  AST-level shrinker를 만든다.
  statement 제거, expression 단순화, constant 축소, branch 제거를 지원한다.

Step 6.
  failure case를 자동 저장하고 regression test로 승격한다.

Step 7.
  그다음 Koen Claessen식 score를 넣는다.
  target은 equivalence 자체가 아니라 “equivalence violation”이다.
  violation이면 score 0, invalid면 ∞, pass이지만 위험하면 작은 score를 준다.

Step 8.
  corpus-guided mutation loop를 만든다.
  새로운 feature coverage나 낮은 score를 주는 program을 corpus에 남긴다.

Step 9.
  zero initialization, arrays, structs, function calls, short-circuit처럼
  translator/semantics가 틀리기 쉬운 feature를 순차적으로 generator에 추가한다.

Step 10.
  CI에는 small fuzz를 넣고, nightly에는 long fuzz를 돌린다.
```

가장 중요한 설계 원칙은 이것입니다.

```text
Coq는 oracle이 아니라 test subject의 일부다.
Go compiler/runtime이 oracle이다.
Fuzzer는 gofile.go와 runtime input을 만들고,
두 실행 path의 observable behavior를 differential하게 비교한다.
```

그리고 Koen Claessen식 접근의 핵심은 이것입니다.

```text
Bool property:
  equivalent? yes/no

Claessen-style objective:
  counterexample에 얼마나 가까운가?
```

따라서 처음에는 단순 QuickCheck식 differential testing으로 시작하고, 그 위에 `Score`, `Corpus`, `Mutate`, `Shrink`를 얹는 방식이 가장 안전합니다.

[1]: https://dl.acm.org/doi/10.1145/351240.351266?utm_source=chatgpt.com "a lightweight tool for random testing of Haskell programs"
[2]: https://en.wikipedia.org/wiki/QuickCheck?utm_source=chatgpt.com "QuickCheck"

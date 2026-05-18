# 지침서

우리는 이미 렉서 생성기(`src/LGS/Main.hs`), 파서 생성기(`src/PGS/Main.hs`)를 자체적으로 갖추었고, 람다 프롤로그의 방언 구현체(Hol ALPHA2)도 가지고 있다.
사용자는 다음 계획들을 구상 중이며, claude에게 모든 파일을 읽을 수 있는 권한과 {`claude.md`, `LICENSE`, `ppap.cabal`, `stack.yaml`, `stack.yaml.lock`}를 제외한 모든 문서 및 코드를 편집할 수 있는 권한을 부여한다.
또한, claude는 궁금한 것은 얼마든지 사용자에게 물어볼 수도 있고, 언제든지 [나의 계획들]을 실현하기 위해 필요한 새로운 단기계획을 시작시킬 것을 제안할 수 있다.

## 코딩 가이드라인

### 무조건 지켜야 하는 사항
1. 하늘이 무너져도 절대 unsafe류를 쓰지 말 것.

### 권고만 하는 사항
1. let in을 지양하고 where을 쓸 것. do 표기법 안에서의 let은 허용함.
1. let in은 쓰더라도
```hs
let x1 = t1 in
let x2 = t2 in
body
```
와 같이 쓰고
```hs
let x1 = t1
    x2 = t2
in body
```
와 같이 쓰지는 말것.
1. 하스켈 코드의 인덴테이션은 항상 4의 배수일 것.
1. 되도록이면 여러 줄 대신 긴 한줄로 출력할 것.

## 나의 계획들

1. 프로젝트 `LoL`: CIC 타입 체커와 그것을 기반으로 하는 대화형 증명보조기.

2. 프로젝트 `Hol`: 1을 만들 수 있는 람다 프롤로그(의 방언) 인터프리터와 그것의 하스켈 API.

## 단기 계획 목록

1. `Hol BETA1` (완료됨):
   - 우선적으로 `doc/HolBETA1.txt` 참고할 것. 또한, claude는 `doc/HolBETA1.txt`를 편집할 수 있다.
   - Hol ALPHA2를 상위호환으로 가져간다는 느낌으로 구현하되 필요하면 적극적으로 구조를 바꿔도 됨. 단, 테스트 {`einstein.sh`(성능 테스트), `fi.sh`(`=>` 의미론,산술 의미론 체크), `lbeta.sh`(hopu 체크)}를 통과해야 함.
   - (폐기됨) 실행하는 동안 산술 제약(Presburger arithmetic을 기반으로 함, `doc/HolBETA1.txt`을 참고할 것)의 무모순성을 확인하는 로직을 내장하기. 이때, 솔버는 `src/Calc/Presburger/Internal.hs`를 인용하라.
   - 원조 람다 프롤로그식 전위/중위 커스텀 노테이션을 다룰 수 있게 하기. 단, 런타임에 커스텀 노테이션을 그대로 보여줄 수 있어야 함.
   - 매크로 기능 지원(Coq의 abbrevation과 비슷하게). 그 예로 list char를 string로 단축한다.
   - 고급테크닉이지만, deBruijn index를 쓰되 named-lambda를 쓰는 것도 가능할까? (마치 Coq처럼).
   - 실행하는 동안 산술 제약을 모은다. 입력받은 문자열을 파싱하여, 주어진 산술 논리식이 현재 산술 제약들로부터 도출가능한지를 presburger (string -> o)라는 술어를 지원한다. 암묵적으로 매 호출마다 `presburger "_|_", !, fail`이 있는 것으로 간주하는 건 어떨까? 이때, 솔버는 `src/Calc/Presburger/Internal.hs`를 인용하라.
   - 디버깅하는 동안, 대화형으로 flexible variable (LVar)를 instantiate할 수 있게 하는 기능도 만들고 싶다. 이는 대화형 증명보조기의 택틱을 구현하는 데 핵심이 될 기술이다.

1. `Hol BETA2` (진행 중):
   1. 현재 Task들:
      1. (완료됨) (C) Multi-head: parser ampersand production + Desugarer body cloning
      2. (진행 중) (A) Module system: module/import keywords + ModuleLoader.hs + C1-C5
      3. (대기 중) (B) SLoc threading: _sloc field + Header module name + debug line
   2. 추가 사항:
      - (대기 중) `:constraint X > 3.` 같은 기능을 넣고 싶다 (아직 이 기능이 없다면).
      - (대기 중) 새로운 기능: symbolic calculus. 예: `Y : (C : (|- nat), x : nat |- nat)`일 때 `Y is C * (x + 1) * (x + 2)` => `Y := C * x * x + 3 * C * x + 2 * C`.
        ```
        main C :- pi x\ sigma Y\ Y is C * (x + 1) * (x + 2), debug "".
        ```
   3. 확인할 점:
      1. `A :- (pi x\ A1 & A2 :- G2) => G.` 같은 게 잘 돌아가는가? 내 생각에는 돌아가야 함---예를 들면, `A :- ((pi x\ A1 :- G2) => ((pi x\ A2 :- G2) => G)).`와 같아야 함.
      1. 이외의 Multi-head에서 발생할 수 있는 문제점.

1. `Hol V1` (대기 중): Hol 프로젝트 정식 넘버링 (v1.0.0):
   - 기존의 인터프리터 대신, 성능을 높이기 위해 (하스켈로 짜여진) bytecode를 생성하는 컴파일러 및 그 실행머신({`src/X/machine.h`, `src/X/machine.c`})을 만드는 것은 어떨까? 현재 기능을 유지한 채로 [`Teyjus 2`](https://github.com/teyjus/teyjus)와 비슷한 성능을 내고 싶다 (`einstein.sh` 실행 시 real이 1초 미만이 되게끔).
   - `LoL BETA1`의 인터프리터를 만들 수 있는 하스켈 API도 제공해야 한다.

1. `LoL ALPHA1` (대기 중): CIC 기반의 증명 스크립트 언어. tactic을 지원하지 않는다.

1. `Hol V2` (대기 중): `LoL BETA1`의 인터프리터를 만들 수 있게 하는 것이 최종 목표이다. [elpi](https://github.com/LPCIC/elpi)처럼 `main` 함수를 만들 것.

1. `LoL BETA2` (대기 중): `LoL ALPHA1`을 계승한, CIC 기반의 증명 스크립트 언어. tactic을 지원한다.

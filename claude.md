# 지침서

우리는 이미 렉서 생성기(`src/LGS/Main.hs`), 파서 생성기(`src/PGS/Main.hs`)를 자체적으로 갖추었고, 람다 프롤로그의 방언 구현체(Hol ALPHA2)도 가지고 있다.
사용자는 다음 계획들을 구상 중이며, claude에게 모든 파일을 읽을 수 있는 권한과 {`claude.md`, `LICENSE`, `ppap.cabal`, `stack.yaml`, `stack.yaml.lock`}를 제외한 모든 문서 및 코드를 편집할 수 있는 권한을 부여한다.
또한, claude는 궁금한 것은 얼마든지 사용자에게 물어볼 수도 있고, 언제든지 [나의 계획들]을 실현하기 위해 필요한 새로운 단기계획을 시작시킬 것을 제안할 수 있다.

## 나의 계획들

1. 프로젝트 `LoL`: CIC 타입 체커와 그것을 기반으로 하는 대화형 증명보조기.

2. 프로젝트 `Hol`: 1을 만들 수 있는 람다 프롤로그(의 방언) 인터프리터와 그것의 하스켈 API.

## 단기 계획 목록

1. `Hol BETA1` (완료됨):
   - 우선적으로 `doc/HolBETA1.txt` 참고할 것. 또한, claude는 `doc/HolBETA1.txt`를 편집할 수 있다.
   - Hol ALPHA2를 상위호환으로 가져간다는 느낌으로 구현하되 필요하면 적극적으로 구조를 바꿔도 됨. 단, 테스트 {`einstein.sh`(성능 테스트), `fi.sh`(`=>`의 의미론, 산술 의미론 체크), `lbeta.sh`(hopu 체크)}를 통과해야 함.
   - (폐기됨) 실행하는 동안 산술 제약(Presburger arithmetic을 기반으로 함, `doc/HolBETA1.txt`을 참고할 것)의 무모순성을 확인하는 로직을 내장하기. 이때, 솔버는 `src/Calc/Presburger/Internal.hs`를 인용하라.
   - 원조 람다 프롤로그식 전위/중위 커스텀 노테이션을 다룰 수 있게 하기. 단, 런타임에 커스텀 노테이션을 그대로 보여줄 수 있어야 함.
   - 매크로 기능 지원(Coq의 abbrevation과 비슷하게). 그 예로 list char를 string로 단축한다.
   - 고급테크닉이지만, deBruijn index를 쓰되 named-lambda를 쓰는 것도 가능할까? (마치 Coq처럼).
   - 실행하는 동안 산술 제약을 모은다. 입력받은 문자열을 파싱하여, 주어진 산술 논리식이 현재 산술 제약들로부터 도출가능한지를 presburger (string -> o)라는 술어를 지원한다. 암묵적으로 매 호출마다 `presburger "_|_", !, fail`이 있는 것으로 간주하는 건 어떨까? 이때, 솔버는 `src/Calc/Presburger/Internal.hs`를 인용하라.
   - 디버깅하는 동안, 대화형으로 flexible variable (LVar)를 instantiate할 수 있게 하는 기능도 만들고 싶다. 이는 대화형 증명보조기의 택틱을 구현하는 데 핵심이 될 기술이다.

1. `Hol BETA2` (진행 중):
   1. 발견된 버그 목록:
      1. ★ (미해결) `Hol BETA1`과 `Hol BETA2` 모두 `fib.sh`에서 오답이 나옴. 정답은 `N := 12`; `N := 1.`; `N := 0`임. `Hol ALPHA2`는 이런 문제가 없음. 테스트 케이스를 `Test/`에 추가할 것.
   2. (진행 중) 추가적인 구현 사항:
      3번 사항과 4번 사항은 다음 버전에 구현하거나 안 구현해도 괜찮지만, 1번 사항과 2번 사항은 이번 버전에서 구현하고 싶다. 5번 사항과 6번 사항은 이번 버전에 넣을지 다음 버전(`Hol V1`)에 넣을지 고민 중이다. 각 사항에 대해 claude의 의견을 듣고 싶다.
      1. (대기 중) 다음의 primitive 술어 추가할 것: `print`, `read`.
         ```
         type print (A -> o). % X := 3일 때 `print X`하면, 3을 출력함.
         type read (A -> o). % X가 unbounded일 때 `read X`하면, X := 3가 됨.
         ```
         debugger나 assign이 이미 있긴 하지만, `print`와 `read`도 필요하다고 생각한다 (디버그 모드에 있지 않고 싶은 때가 있을 수도 있으니까).
      2. (대기 중) 새로운 기능: symbolic calculus. 예: `Y : (C : (|- nat), x : nat |- nat)`일 때 `Y is C * (x + 1) * (x + 2)` => `Y := C * x * x + 3 * C * x + 2 * C`. 기능을 만들었다고 쳤을 때, 다음 쿼리로 확인가능하다:
         ```
         ?- sigma\ C pi x\ sigma Y\ Y is C * (x + 1) * (x + 2), debug "".
         ```
         그러나, 이 기능을 추가할 때, 기존의 의미론과 조화로운지를 반드시 검토해야 한다.
      3. (대기 중) 분수(fraction) and/or 부동소수점(float) 자료형 추가. 굳이 필요할까 하는 생각이 든다. 게다가, 이 기능을 넣는다면 solver 만들어야 할 텐데, 그건 무리일 것 같다.
      4. (대기 중) `:constraint X > 3.` 같이 산술제약을 가하는 기능을 넣고 싶다 (아직 이 기능이 없다면).
      5. (대기 중) 아무래도 타입 메세지 출력을 너무 못하는 듯. GHC식 타입체킹 알고리즘 적용 가능할까?
      6. (대기 중) Z.Doc(Z.Text.Doc 아님)을 이용하여 에러 메세지 깔끔하게 출력하기.
   3. (대기 중) 확인할 점:
      - (대기 중) `A :- (pi x\ A1 & A2 :- G2) => G.` 같은 게 잘 돌아가는가? 내 생각에는 돌아가야 함---예를 들면, `A :- ((pi x\ A1 :- G2) => ((pi x\ A2 :- G2) => G)).`와 같아야 함.
      - (대기 중) 위 사항 이외의 Multi-head에서 발생할 수 있는 문제점 생각하기.
      - (대기 중) 프로젝트 완료 후, 코딩 가이드라인(`claude.md`의 부록 A)에 따라 `Hol BETA 1`과 `Hol BETA 2` 모두 리팩토링할 것. 포맷팅이 내 마음에 들지 않음.

1. `Hol V1` (대기 중):
   Hol 프로젝트의 첫 번째 정식 넘버링 (v1.0.0).
   - 인터프리터 외에도, 성능을 높이기 위해 (하스켈로 짜여진) bytecode를 생성하는 컴파일러 및 그 실행머신({`src/X/machine.h`, `src/X/machine.c`})을 만드는 것은 어떨까? 현재 기능을 유지한 채로 [`Teyjus 2`](https://github.com/teyjus/teyjus)와 비슷한 성능을 내고 싶다 (`einstein.sh` 실행 시 real이 1초 미만이 되게끔).
   - `LoL ALPHA1`의 인터프리터를 만들 수 있는 하스켈 API도 제공해야 한다.

1. `LoL ALPHA1` (대기 중):
   CIC 기반의 증명 스크립트 언어.
   - tactic을 지원하지 않는다.
   - 과연 Hol V1 API로 만들 수 있을까? 애초에 방향이 틀린 건 아닌지 걱정됨.

1. `Hol V2` (대기 중):
   Hol 프로젝트의 두 번째 정식 넘버링 (v2.0.0). `Hol V1`의 완전한 상위호환.
   - 이것의 API로 `LoL BETA1`의 인터프리터를 만들 수 있게 하는 것이 최종 목표이다.
   - [`elpi`](https://github.com/LPCIC/elpi)처럼 `main` 함수를 만들 것.

1. `LoL BETA2` (대기 중):
   `LoL ALPHA1`을 계승한, CIC 기반의 증명 스크립트 언어.
   - 대화형 스크립트 실행기를 만드는 것이 목표이다.
   - tactic을 지원한다.

## 부록 A. 하스켈 코드 작성 가이드라인

읽은 후 궁금한 거나 모순되는 거 물어보시오.

### 무조건 지켜야 하는 사항
1. 하늘이 무너져도 절대 unsafe류는 쓰면 안 된다.
1. C ffi 작업은 디렉토리 `src/X/`에서 한다. 즉, 모든 C 코드와 그 하스켈 래퍼는 디렉토리 `src/X/` 안에 있어야 한다.
1. 하스켈 코드의 인덴테이션은 항상 4의 배수일 것.
1. 튜플이 아닌 소괄호 안의 식은 무조건 1줄로 쓸 것.

### 권장 사항
1. let in을 지양하고 where을 쓸 것. do 표기법 안에서의 let은 허용함. 예:
   ```hs
   foo bar = case bar of
       Bar x ->
           let y = x + 2
           in y * 2
   ```
   를 지양하고
   ```hs
   foo bar
       = case bar of
           Bar x -> y * 2 where
               y = x + 2
   ```
   와 같이 쓴다.
1. 되도록이면 짧은 여러 줄 대신 긴 한 줄로 작성할 것. 예: `mapM_ (\x -> ...) xs`은 한 줄 안에 쓴다. do 노테이션에서 `<pat> <- <term>`도 한 줄에 쓴다. `Record { fld1 = ..., ..., fldn = ... }`도 단독으로 나타나지 않고 인자인 경우 한 줄로 길게 쓸 것:
   ```hs
   foo x y = bar (Baz { baz1 = f x, baz2 = g y })
   ```
   처럼 쓰고
   ```hs
   foo x y = bar $ Bar
       { baz1 = f x
       , baz2 = g y
       }
   ```
   처럼은 쓰지 않는다.
1. let in은 쓰더라도,
   ```hs
   let x1 = t1 in
   let x2 = t2 in
   body
   ```
   와 같이 쓰고,
   ```hs
   let x1 = t1
       x2 = t2
   in body
   ```
   와 같이 쓰지는 말 것.
   (do 표기법 안의 let은 해당 안 됨.)
1. `where`을 이렇게 쓸 것:
   ```hs
   foo x y = ... where
       go z = ... 

   bar x y
       | ... = ...
       | otherwise = ...
       where
           go z = ...
   ```
1. align하지 말 것. 예:
   ```hs
   foo (Just x) = ...
   foo Nothing  = ...
   ```
   를 지양하고
   ```hs
   foo (Just x) = ...
   foo Nothing = ...
   ```
   를 지향한다.
1. 문자열을 출력할 때, `String` 대신 `ShowS`을 쓰고, `++` 대신 `.`를 쓸 것. (`strstr`은 당연히 써야 함.) 예:
   ```hs
   helloWord :: ShowS
   helloWord = strcat
       [ strstr "hello" . nl
       , strstr "world" . nl
       ]
   ```
1. `if b then e1 else e2`는 아예 1줄로 쓰거나
   ```hs
   if b then
       e1
   else
       e2
   ```
   또는
   ```hs
   if b
       then e1
       else e2
   ```
   와 같이 쓸 것.
   그러나 `else if`는
   ```hs
   if b1 then
       e1
   else if b2 then
       e2
   else
       e3
   ```
   와 같이 쓸 것.

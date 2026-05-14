# 지침서

우리는 이미 렉서 생성기(`src/LGS/Main.hs`), 파서 생성기(`src/PGS/Main.hs`)를 자체적으로 갖추었고, 람다 프롤로그의 방언 구현체(Hol ALPHA2)도 가지고 있다.
사용자는 다음 계획들을 구상 중이며, claude에게 {`claude.md`, `LICENSE`, `ppap.cabal`}를 제외한 모든 문서 및 코드를 편집할 수 있는 권한을 부여한다.
또한, claude는 궁금한 것은 얼마든지 사용자에게 물어볼 수도 있고, 언제든지 [나의 계획들]을 실현하기 위해 필요한 새로운 단기계획을 시작시킬 것을 제안할 수 있다.

## 나의 계획들

1. 프로젝트 `LoL`: CIC 타입 체커와 그것을 기반으로 하는 대화형 증명보조기.

2. 프로젝트 `Hol`: 1을 만들 수 있는 람다 프롤로그(의 방언) 인터프리터와 그것의 하스켈 API.

## 단기 계획 목록

1. `Hol BETA1`:
   - 우선적으로 `doc/HolBETA1.txt` 참고할 것. 또한, claude는 `doc/HolBETA1.txt`를 편집할 수 있다.
   - Hol ALPHA2를 상위호환으로 가져간다는 느낌으로 구현하되 필요하면 적극적으로 구조를 바꿔도 됨. 단, 테스트 `einstein.sh`, `fi.sh`, `lbeta.sh`를 통과해야 함.
   - (폐기됨) 실행하는 동안 산술 제약(Presburger arithmetic을 기반으로 함, `doc/HolBETA1.txt`을 참고할 것)의 무모순성을 확인하는 로직을 내장하기. 이때, 솔버는 `src/Calc/Presburger/Internal.hs`를 인용하라.
   - 원조 람다 프롤로그식 전위/중위 커스텀 노테이션을 다룰 수 있게 하기. 단, 런타임에 커스텀 노테이션을 그대로 보여줄 수 있어야 함.
   - 매크로 기능 지원(Coq의 abbrevation과 비슷하게). 그 예로 list char를 string로 단축한다.
   - 고급테크닉이지만, deBruijn index를 쓰되 named-lambda를 쓰는 것도 가능할까? (마치 Coq처럼).
   - 실행하는 동안 산술 제약을 모은다. 입력받은 문자열을 파싱하여, 주어진 산술 논리식이 현재 산술 제약들로부터 도출가능한지를 presburger (string -> o)라는 술어를 지원한다. 암묵적으로 매 호출마다 `presburger "_|_", !, fail`이 있는 것으로 간주하는 건 어떨까? 이때, 솔버는 `src/Calc/Presburger/Internal.hs`를 인용하라.
   - 디버깅하는 동안, 대화형으로 flexible variable (LVar)를 instantiate할 수 있게 하는 기능도 만들고 싶다. 이는 대화형 증명보조기의 택틱을 구현하는 데 핵심이 될 기술이다.

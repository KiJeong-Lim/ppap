# LLM Guideline

이 문서는 LLM이 이 저장소의 Haskell 코드를 수정할 때 따라야 할 로컬 스타일 지침이다. 기준 예시는 `src/Project/A/`, `src/LGS/`, `src/PGS/`이다.

## 기본 원칙

기존 코드의 결을 우선한다. 의미를 바꾸지 않는 포맷팅/리팩토링을 할 때도, 자동 포맷터식 정렬보다 이 저장소의 손으로 쓴 모양을 따른다.

`claude.md` 부록 A의 하스켈 코드 작성 가이드라인을 함께 따른다. 특히 들여쓰기는 항상 4의 배수로 맞추고, 튜플이 아닌 소괄호 안의 식은 한 줄로 둔다.

짧은 여러 줄보다 긴 한 줄이 자연스러운 경우에는 긴 한 줄을 선호한다. 예를 들어 `mapM_ (\x -> ...) xs`, do 표기법의 `<pat> <- <term>`, 인자로 쓰이는 `Record { fld1 = ..., fld2 = ... }`는 억지로 여러 줄로 풀지 않는다.

생성된 파일은 함부로 고치지 않는다. 예를 들어 `PlanHolLexer.hs`, `PlanHolParser.hs`처럼 LGS/PGS가 만든 파일은 원본 `.txt` 생성문법을 수정한 뒤 재생성하는 것이 원칙이다.

## 모듈

공개 API가 분명한 진입점 모듈은 export list를 둘 수 있다.

```hs
module Project.A.Main
    ( main
    , mainWithArgs
    ) where
```

내부 모듈은 보통 export list 없이 둔다.

```hs
module Project.A.Types where
```

## 함수 배치

본문이 조금이라도 길면 `=`를 다음 줄에 둔다.
같은 이름의 여러 방정식이나 의미상 한 묶음인 자매 정의에서는, 하나라도 `=`를 다음 줄에 두면 나머지도 같이 다음 줄에 둔다.

```hs
mainWithArgs :: [String] -> IO ()
mainWithArgs args
    = case parseCommand args of
        Help -> putStr helpText
        One options -> runOne options
        Fuzz options -> runFuzz options
```

짧은 식은 한 줄로 둬도 된다.

```hs
configFromOptions :: Options -> RunConfig
configFromOptions options = defaultRunConfig { cfgWorkDir = optWorkDir options }
```

`where`를 선호한다. `let ... in`은 되도록 피한다. do 안의 짧은 `let`은 허용한다.
그래도 `let ... in`을 써야 한다면 여러 바인딩을 세로 정렬하지 말고, `let x1 = t1 in let x2 = t2 in body`처럼 한 바인딩씩 이어 쓴다.

줄바꿈이 필요한 `++` 체인은 `++`로 계속 잇지 말고 `concat [...]`으로 묶는다. 한 줄에 자연스럽게 들어가는 짧은 `++` 체인은 그대로 둘 수 있다.

```hs
stringOptionMaybe :: String -> [String] -> Maybe String
stringOptionMaybe key rawArgs = go (map normalizeArg rawArgs) where
    prefix = key ++ "="

    go [] = Nothing
    go [arg]
        | prefix `isPrefixOf` arg = Just (drop (length prefix) arg)
        | otherwise = Nothing
```

## 데이터 선언

레코드 생성자는 타입명 다음 줄에 둔다.
record data type 선언에서는 `{ ... }` 블록을 생성자보다 한 단계 더 들여쓰지 않는다. `{`, `,`, `}`는 `= 생성자`와 같은 4칸 들여쓰기 기준에 맞춘다.

```hs
data RuntimeInput
    = RuntimeInput
    { riArgs :: [String]
    , riStdin :: String
    , riEnv :: [(String, String)]
    } deriving (Eq, Ord, Show)
```

단일 필드 `newtype` 레코드는 생성자와 필드 블록을 같은 줄에 둔다.

```hs
newtype Runtime a
    = Runtime { unRuntime :: ReaderT RuntimeEnv IO a }
```

합 타입도 같은 방식으로 쓴다.

```hs
data Termination
    = Terminated
    | TimedOut
    | RuntimeFailed
    deriving (Eq, Ord, Show)
```

짧은 레코드 생성은 한 줄로 유지한다.

```hs
timeoutObs :: Obs
timeoutObs = Obs { obsTermination = TimedOut, obsExitCode = Nothing, obsStdout = "", obsTimedOut = True }
```

## Case, If

`case`는 함수 본문에서 다음처럼 배치한다.

```hs
normalizeArg :: String -> String
normalizeArg arg
    = case stripPrefix "--" arg of
        Just rest -> rest
        Nothing -> arg
```

`if`는 한 줄로 충분하면 한 줄로 쓰고, 길면 다음처럼 자연스럽게 나눈다.

```hs
if not (processSucceeded coqcResult) then
    return (failedAfterCoqc translatorLog coqcLog (CoqError coqcLog))
else do
    ...
```

여러 줄 `if`에서는 되도록 `if 조건 then`을 한 줄에 두고, `then`만 다음 줄에 따로 세우지 않는다.

불필요하게 계층을 깊게 만들지 않는다.

## 문자열 출력

출력용 문자열 조립은 가능하면 `ShowS`, `strstr`, `strcat`, `nl`을 쓴다.

```hs
helpText :: String
helpText = helpText' ""

helpText' :: ShowS
helpText' = strcat
    [ strstr "Project A differential fuzzing" . nl
    , nl
    , strstr "Commands:" . nl
    ]
```

일반 데이터 처리나 파일 경로 조립에는 `++`를 써도 된다.

## 리스트와 긴 식

짧은 리스트/레코드/인자는 한 줄에 둔다.

```hs
seedJson tc = Json.object [Json.field "caseId" (Json.int (tcCaseId tc)), Json.field "seed" (Json.int (tcSeed tc)), Json.field "size" (Json.int (tcSize tc))]
```

하지만 여러 분기를 합치는 경우에는 `concat`과 리스트 블록을 써서 구조를 드러낸다.

```hs
SIf cond thn els -> concat
    [ [indent depth ++ "if " ++ prettyExpr cond ++ " {"]
    , concatMap (prettyStmt (depth + 1)) thn
    , if null els then [indent depth ++ "}"] else [indent depth ++ "} else {"] ++ concatMap (prettyStmt (depth + 1)) els ++ [indent depth ++ "}"]
    ]
```

## 주석

LLM식 장황한 설명 주석은 피한다. 코드만으로 읽히는 내용은 주석으로 쓰지 않는다.

좋지 않은 예:

```hs
-- This function updates the map by inserting the new value and returning the updated state.
```

주석은 다음 경우에만 짧게 둔다.

```text
1. 생성 코드와 수작업 코드의 경계
2. 의미론적 정책
3. 나중에 깨지기 쉬운 불변식
4. 외부 도구/파일 형식과의 약속
```

## 금지/주의

`unsafe` 계열은 쓰지 않는다.

C FFI 작업은 `src/X/` 안에서만 한다.

기존 사용자가 만든 변경을 되돌리지 않는다.

생성 파일을 직접 손으로 고치는 것을 피한다.

의미 변경 없이 스타일만 바꾸는 작업이라도 반드시 빌드 또는 관련 smoke test를 돌린다.

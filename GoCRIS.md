# GoCRIS

Coq 퍼징 테스트를 Koen Claessen식으로 접근하고 싶습니다.
Coq 퍼징 테스트 목표는 [gofile.go 가 임의로 주어질 때 gofile.go를 Go compiler로 돌려서 바이너리를 실행해 얻는 외부에서 observable한 behavior와
```
gofile.go --[ my translator ]-> gofile.v (itree semantics) --[ Coq->Haskell extraction ]-> gofile.hs
```
의 패스로 얻은 gofile.hs의 외부에서 observable한 behavior가 같아야 한다]는 것을 검증하는 것입니다.
gofile.v를 매번 생성하고 coqc 컴파일하고 extraction하여 비교하는 방식으로 진행하고 싶은데, 전체 plan을 그려주세요.

module Calc.ControlSystem.Util where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Math.V1

type MyNode = String

type MyExpr = ElemExpr Double

type Diagram = Map.Map (MyNode, MyNode) MyExpr

data System
    = System
        { _entry_point :: MyNode
        , _main_output :: MyNode
        , _get_diagram :: Diagram
        }
    deriving ()

instance Show (System) where
    showsPrec _ sys = ppunc "\n"
        [ strstr "entry-point = " . shows (_entry_point sys)
        , strstr "main-output = " . shows (_main_output sys)
        , strstr "diagram = " . ppunc "\n" [ shows v_from . strstr " ~~[" . shows e_expr . strstr "]~> " . shows v_to | ((v_from, v_to), e_expr) <- Map.toAscList (_get_diagram sys) ]
        ]

module Jasmine.Alpha2.Solver.Hopu where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Data.Function
import Jasmine.Alpha2.Header.Export

type Disagreement metavar ivar constr = (Term metavar ivar constr, Term metavar ivar constr)

type Spine metavar ivar constr = ((metavar, Subst metavar ivar constr), [Term metavar ivar constr])

data HopuE
    = NotAPattern
    deriving (Eq, Show)

class Eq n => NameLike n where

class Eq c => ConstrLike c where

unfoldNApp :: Term u n c -> (Term u n c, [Term u n c])
unfoldNApp = undefined

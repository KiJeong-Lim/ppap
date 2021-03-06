module Jasmine.Alpha1.Header.TermNode.Render where

import Jasmine.Alpha1.Header.TermNode
import Jasmine.Alpha1.Header.Util
import Z.Utils

data IdentifierViewer view
    = Cannon { _view_prec :: Precedence, _view_content :: String }
    | Prefix { _view_prec :: Precedence, _view_content :: String, _view_right :: view }
    | InfixL { _view_prec :: Precedence, _view_left :: view, _view_content :: String, _view_right :: view }
    | InfixN { _view_prec :: Precedence, _view_left :: view, _view_content :: String, _view_right :: view }
    | InfixR { _view_prec :: Precedence, _view_left :: view, _view_content :: String, _view_right :: view }
    deriving ()

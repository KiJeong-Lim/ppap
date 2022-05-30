module Jasmine.Alpha2.Header.TermNode where

type CtxTyp metavar ivar constr = (LCtx metavar ivar constr, Term metavar ivar constr) -- contextual type

type LCtx metavar ivar constr = [LCtxItem metavar ivar constr] -- local context

type MCtx metavar ivar constr = [MCtxItem metavar ivar constr] -- meta-context

type Subst metavar ivar constr = [Term metavar ivar constr] -- suspensed substitution

data Term metavar ivar constr
    = LVar (metavar, Subst metavar ivar constr)
    | NVar (ivar)
    | NCon (constr)
    | NApp (Term metavar ivar constr) (Term metavar ivar constr)
    | NLam (ivar) (Term metavar ivar constr)
    | NAll (ivar) (Term metavar ivar constr)
    | NAst
    deriving (Eq, Show)

data LCtxItem metavar ivar constr
    = NVarOfNoRef { _lctx_var :: Term metavar ivar constr, _lctx_var_typ :: Term metavar ivar constr }
    | NVarWithRef { _lctx_var :: Term metavar ivar constr, _lctx_var_typ :: Term metavar ivar constr, _lctx_ref :: Term metavar ivar constr }
    deriving (Eq, Show)

data MCtxItem metavar ivar constr
    = MCtxOfNoRef { _mctx_var :: Term metavar ivar constr, _mctx_var_typ :: CtxTyp metavar ivar constr }
    | MCtxWithRef { _mctx_var :: Term metavar ivar constr, _mctx_var_typ :: CtxTyp metavar ivar constr, _mctx_ref :: Term metavar ivar constr }
    deriving (Eq, Show)

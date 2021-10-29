# Jasmine

- A new dialect of `λProlog`

## The syntax of Jasmine

```
<Program> -> <ModuleDecl> <ImportDecl>* <SubmoduleDefn>*

<Query> -> "?-" <fmapal> $nl
<Query> -> <Command>

<ModuleDecl> -> "module" <ModuleName> $nl

<ImportDecl> -> "import" <ModuleName> $nl

<SubmoduleDefn> -> "submodule" <SubmoduleName> "where" $nl $tab <OpenDecl>* <TopLevelStmt>* $untab

<TopLevelStmt> -> <DataDefn>
<TopLevelStmt> -> <TypeDefn>
<TopLevelStmt> -> <PredDefn>

<OpenDecl> -> "open" <SubmoduleName> $nl

<DataDefn> -> "data" <TypeConstrName> <TypeParameter>* ":" <KindExpr0> "where" $nl $tab <DataConstrDecl>* $untab

<DataConstrDecl> -> <DataConstrName> ":" <TypeExpr0> $nl

<TypeDefn> -> "type" <TypeOperName> <TypeParameter>* "=" <TypeExpr0> $nl

<TypeParameter> -> "(" <TypeVar> ":" <KindExpr0> ")"

<PredDefn> -> "pred" <PredName> ":" <TypeExpr0> "where" $nl $tab <PredStmt>* $untab

<PredStmt> -> <Rule> $nl

<Goal> -> <TermExpr0>

<Rule> -> <TermExpr0>
```

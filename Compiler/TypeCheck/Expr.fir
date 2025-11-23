import [Compiler/Ast]


checkExpr(expr: Expr, pgm: Program, env: FunTcEnv) (ty: Ty, binds: HashMap[LocalId, Ty]) / TypeError:
    match expr:
        Expr.Var(VarExpr(id, userTyArgs, tyArgs)):
            assert(tyArgs.isEmpty())

            match id.def():
                VarDefIdx.Local:
                    assert(userTyArgs is Option.None)
                    (ty = env.local(id.name), binds = HashMap.empty())

                VarDefIdx.Top(topVarIdx):
                    let scheme = pgm.scheme(topVarIdx)
                    panic("TODO")

        Expr.ConstrSelect(..): panic("TODO")

        Expr.FieldSelect(..): panic("TODO")

        Expr.MethodSelect(..): panic("TODO")

        Expr.ConstrSelect(..): panic("TODO")

        Expr.AssocFnSelect(..): panic("TODO")

        Expr.Call(..): panic("TODO")

        Expr.Int(..): panic("TODO")

        Expr.Str(..): panic("TODO")

        Expr.Char(..): panic("TODO")

        Expr.Self(..): panic("TODO")

        Expr.BinOp(..): panic("TODO")

        Expr.UnOp(..): panic("TODO")

        Expr.Record(..): panic("TODO")

        Expr.Return(..): panic("TODO")

        Expr.Match(..): panic("TODO")

        Expr.If(..): panic("TODO")

        Expr.Fn_(..): panic("TODO")

        Expr.Is(..): panic("TODO")

        Expr.Do(..): panic("TODO")

        Expr.Seq(..): panic("TODO")

        Expr.Paren(..): panic("TODO")

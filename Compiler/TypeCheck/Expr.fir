import [Compiler/Ast]


# TODO: the returned types in `checkExpr` should be unified with the expected
# type. Maybe have two `checkExpr`s: one that always returns the inferred type,
# and another that takes the inferred type nad unifies with the expected type.


## Returns the type of the expression, and binders that the expression binds.
##
## Only boolean expressions bind variables.
##
## - `<expr> is <pat>` binds the variables that `<pat>` binds.
##
## - `<expr1> and <expr2>` binds the variables that `<expr1>` and `<expr2>`
##   bind. `<expr1>` and `<expr2>` need to bind disjoint set of variables.
##
## Other expressions don't bind any variables.
##
## Variables bound in `if` and `while` conditionals are used in the bodies.
checkExpr(
    expr: Expr,
    pgm: Program,
    env: FunTcEnv,
    expectedTy: Option[Ty],
    level: U32,
    loopStack: Option[Vec[LocalId]],
) (ty: Ty, binds: HashMap[LocalId, Ty]) / TypeError:
    match expr:
        Expr.Var(expr):
            _checkVarExpr(expr, pgm, env, expectedTy, level, loopStack)

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


_checkVarExpr(
    varExpr: VarExpr,
    pgm: Program,
    env: FunTcEnv,
    expectedTy: Option[Ty],
    level: U32,
    loopStack: Option[Vec[LocalId]],
) (ty: Ty, binds: HashMap[LocalId, Ty]) / TypeError:
    let id = varExpr.id
    let userTyArgs = varExpr.userTyArgs
    let exprLoc = pgm._modules.get(env._modIdx._idx).loc(varExpr)

    assert(varExpr.tyArgs.isEmpty())

    match id.def():
        VarDefIdx.Local:
            if userTyArgs is Option.Some(..):
                throw(
                    TypeError(
                        loc = exprLoc,
                        msg =
                            "Local variables can't have type parameters, but \``id.name`\`is passed type arguments",
                    ),
                )
            (ty = env.local(id.name), binds = HashMap.empty())

        VarDefIdx.Top(topVarIdx):
            let scheme = pgm.scheme(topVarIdx)

            let ty = if userTyArgs is Option.Some(userTyArgs):
                # This should be syntax error:
                assert(not userTyArgs.args.isEmpty())

                if scheme.qvars.len() != userTyArgs.args.len():
                    throw(
                        TypeError(
                            loc = exprLoc,
                            msg =
                                "Variable \``id.name`\` takes `scheme.qvars.len()` type arguments, but applied to `userTyArgs.args.len()`",
                        ),
                    )

                let userTyArgsConverted: Vec[Ty] = Vec.fromIter(
                    userTyArgs.args.iter().map(
                        |ty: Type| Ty:
                            convertAstTy(
                                pgm.module(env._modIdx),
                                env._termEnv,
                                ty,
                            ),
                    ),
                )

                let ty = scheme.instantiateWithTys(
                    userTyArgsConverted,
                    env._preds,
                    exprLoc,
                )

                varExpr.tyArgs = userTyArgsConverted
                ty
            else:
                let tyAndVars = scheme.instantiate(
                    level,
                    env._varGen,
                    env._preds,
                    exprLoc,
                )
                varExpr.tyArgs = Vec.fromIter(tyAndVars.vars.iter().map(Ty.UVar))
                tyAndVars.ty

            (ty = ty, binds = HashMap.empty())

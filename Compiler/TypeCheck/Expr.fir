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

        Expr.ConstrSelect(expr):
            _checkConExpr(expr, pgm, env, expectedTy, level, loopStack)

        Expr.FieldSelect(..): panic("TODO")

        Expr.MethodSelect(..): panic("TODO")

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

        Expr.Variant(..): panic("TODO")


_checkVarExpr(
    varExpr: VarExpr,
    pgm: Program,
    env: FunTcEnv,
    expectedTy: Option[Ty],
    level: U32,
    loopStack: Option[Vec[LocalId]],
) (ty: Ty, binds: HashMap[LocalId, Ty]) / TypeError:
    let mod = pgm.module(env._modIdx)
    let id = varExpr.id
    let userTyArgs = varExpr.userTyArgs
    let exprLoc = mod.loc(varExpr)

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
                        \(ty: Type) Ty: convertAstTy(mod, env._termEnv, ty,),
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


_checkConExpr(
    con: Constructor,
    pgm: Program,
    env: FunTcEnv,
    expectedTy: Option[Ty],
    level: U32,
    loopStack: Option[Vec[LocalId]],
) (ty: Ty, binds: HashMap[LocalId, Ty]) / TypeError:
    assert(con.tyArgs.isEmpty())

    let mod = pgm.module(env._modIdx)

    let tyCon = pgm.tyCon(con.ty.def())
    let tyConUseSiteName = mod.tokenText(con.ty.token)

    let details = match tyCon.details:
        TyConDetails.Trait(..):
            throw(
                TypeError(
                    loc = mod.loc(con),
                    msg = "Type in constructor selection is a trait",
                ),
            )

        TyConDetails.Type(details): details

    # TODO: This does not support renaming constructors
    let conName = con.constr.map(\(id): mod.idText(id)).unwrapOrElse(
        \(): tyCon.name,
    )

    let scheme = details.cons.get(conName).unwrapOrElse(
        \():
            throw(
                TypeError(
                    loc = mod.loc(con),
                    msg =
                        "Type `tyConUseSiteName` does not have constructor `conName`",
                ),
            ),
    )

    let conTy: Ty = match con.userTyArgs:
        Option.None:
            let (ty, vars) = scheme.instantiate(
                level,
                env._varGen,
                env._preds,
                mod.loc(con),
            )

            con.tyArgs = Vec.fromIter(vars.iter().map(Ty.UVar))

            ty

        Option.Some(args):
            assert(not args.args.isEmpty())
            panic("TODO")

    panic("TODO")


# This function is ported from the interpreter and it's not quite right.
#
# In the interpreter we parse `~C(...)` as a constructor application, rather
# than a variant expression. The fact that this is a variant is reflected in the
# constructor AST.
#
# So we type check `App(~C, ...)` instead of `Var(App(C, ...))`, and then apply
# it to the arguments, and the return type should be a variant of `C`, not just
# `C`.
#
# In the compiler we should parse this as `Var(App(Con(...), ...))`, and then
# have an "inject" function that takes a type (other than a function type) and
# convert it to a variant.
#
# Relevant issue: #238.
#
# Original documentation below:
#
# ty -> [labelOf(ty): ty, ..r] (r is fresh)
#
# Somewhat hackily, we also convert function types that return named types to
# function types that return variants instead, to allow type checking
# `~Foo(args)` by first converting `Foo`'s type to a function type, and then
# applying.
makeVariant(varGen: UVarGen, ty: Ty, level: U32, loc: Loc) Ty:
    let extension = Option.Some(
        Ty.UVar(varGen.newVar(level, Kind.Row(RecordOrVariant.Variant), loc)),
    )

    match ty.normalize():
        Ty.Con(id, ..):
            Ty.Variant(
                cons = HashMap.[id = Vec.empty()],
                extension,
                isRow = Bool.False,
            )

        Ty.App(conId, args):
            Ty.Variant(
                cons = HashMap.[conId = args],
                extension,
                isRow = Bool.False,
            )

        Ty.Fun(args, ret, exn):
            # This part is also ported from the interpreter and while it's not
            # wrong it's also too flexible/permissive. When the type is a
            # function type the return type must be a `Con` or `App`, so we
            # don't need a recursive call, which would handle `Fun`s in return
            # type position.
            return Ty.Fun(args, ret = makeVariant(varGen, ret, level, loc), exn)

        _: panic("Type in variant is not a constructor")

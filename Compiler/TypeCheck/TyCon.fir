import [Compiler/TypeCheck/Ty]


type TyCon(
    ## Name of the type.
    name: Str,

    ## Type parameters with kinds.
    tyParams: Vec[TyParam],

    ## Methods for traits, constructor for sums, fields for products.
    ##
    ## Types can refer to `ty_params` and need to be substituted by the
    ## instantiated the types in `ty_params` before use.
    details: TyConDetails,
)


TyCon.arity(self) U32:
    self.tyParams.len()


## A type parameter with kind.
type TyParam(
    name: Id,
    kind: Kind,
)


#[derive(ToDoc)]
type TyConDetails:
    Trait(TraitDetails)
    Type(TypeDetails)


#[derive(ToDoc)]
type TraitDetails(
    ## Methods of the trait, with optional default implementations.
    methods: HashMap[Str, TraitMethod],
)


#[derive(ToDoc)]
type TraitMethod(
    ## Scheme of the trait method. Can refer to the type parameters of the
    ## trait.
    scheme: Scheme,

    ## The declaration of the trait method. When this has a body, the body is
    ## used as the default implementation of the method.
    ##
    ## This can refer to the type parameters of the trait.
    funDecl: FunDecl,
)


#[derive(ToDoc)]
type TypeDetails(
    ## Names of value constructors of the type.
    cons: Vec[Str],

    ## Whether the type is a sum type.
    ##
    ## A product type will always have one constructor in `cons`.
    ##
    ## A sum type can have any number of constructors in `cons`.
    sum: Bool,
)


# ------------------------------------------------------------------------------
# Generated ToDoc implementations


impl ToDoc[TyConDetails]:
    toDoc(self: TyConDetails) Doc:
        match self:
            TyConDetails.Trait(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TyConDetails.Trait") + Doc.char('(') + args)
            TyConDetails.Type(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TyConDetails.Type") + Doc.char('(') + args)


impl ToDoc[TraitDetails]:
    toDoc(self: TraitDetails) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("methods =")
                + Doc.nested(4, Doc.break_(1) + self.methods.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TraitDetails") + Doc.char('(') + args)


impl ToDoc[TraitMethod]:
    toDoc(self: TraitMethod) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("scheme =")
                + Doc.nested(4, Doc.break_(1) + self.scheme.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("funDecl =")
                + Doc.nested(4, Doc.break_(1) + self.funDecl.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TraitMethod") + Doc.char('(') + args)


impl ToDoc[TypeDetails]:
    toDoc(self: TypeDetails) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("cons =") + Doc.nested(4, Doc.break_(1) + self.cons.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("sum =") + Doc.nested(4, Doc.break_(1) + self.sum.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TypeDetails") + Doc.char('(') + args)

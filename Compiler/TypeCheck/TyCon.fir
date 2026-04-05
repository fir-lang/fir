import [
    Compiler/CompilerAst,
    Compiler/TypeCheck/Ty,
]


#[derive(ToDoc)]
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
#[derive(ToDoc)]
type TyParam(
    name: LocalId,
    kind: Kind,
)


#[derive(ToDoc)]
type TyConDetails:
    Trait(TraitDetails)
    Type(TypeDetails)


TyConDetails.placeholder() TyConDetails:
    TyConDetails.Type(TypeDetails(cons = HashMap.empty(), sum = Bool.False))


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
    #
    # TODO: This will refer to the declaration's module in tokens but we won't
    # have its module at the use sites.
    funDecl: CFunDecl,
)


#[derive(ToDoc)]
type TypeDetails(
    ## Value constructors of the type.
    cons: HashMap[Str, Scheme],

    ## Whether the type is a sum type.
    ##
    ## A product type will always have one constructor in `cons`.
    ##
    ## A sum type can have any number of constructors in `cons`.
    sum: Bool,
)

# Import all modules temporarily to type check all.
import [
    Compiler/Program,
    Compiler/TypeCheck/Convert,
    Compiler/TypeCheck/Error,
    Compiler/TypeCheck/Normalization,
    Compiler/TypeCheck/RowUtils,
    Compiler/TypeCheck/TraitEnv,
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/TyCon,
    Compiler/TypeCheck/TyMap,
    Compiler/TypeCheck/Unification,
]


prepTcEnvs(pgm: Program):
    ()


## The module environment holds type constructors, traits (with impls), and
## associated and top-level functions available in the module.
type ModuleTcEnv(
    ## The traits, with impls.
    _traitEnv: TraitEnv,

    ## Type constructors.
    _cons: HashMap[Str, TyCon],

    ## Top-level function sschemes.
    _topSchemes: HashMap[Str, Scheme],

    ## Associated function schemes.
    # _assocFnSchemes: 
)


type FunTcEnv(
    _modTcEnv: ModuleTcEnv,
)

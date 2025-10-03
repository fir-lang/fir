trait Test[a]:
    fun(self) ()

# args: --typecheck
# expected stderr: tests/TraitImplSelfTyFail.fir:2:5: Trait methods can't have implicit self type

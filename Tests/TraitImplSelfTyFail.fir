trait Test[a]:
    fun(self) ()

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/TraitImplSelfTyFail.fir:2:5: Trait methods can't have implicit self type

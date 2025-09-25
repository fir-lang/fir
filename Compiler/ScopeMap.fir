#[derive(ToDoc)]
type ScopeMap[k, v](
    scopes: Vec[HashMap[k, v]],
)


ScopeMap.fromMap(map: HashMap[k, v]) ScopeMap[k, v]:
    let scopes = Vec.withCapacity(10)
    scopes.push(map)
    ScopeMap(scopes)


ScopeMap.enterScope(self: ScopeMap[k, v]):
    self.scopes.push(HashMap.withCapacity(10))


ScopeMap.exitScope(self: ScopeMap[k, v]) HashMap[k, v]:
    self.scopes.pop().unwrap()


ScopeMap.insert[Hash[k], Eq[k]](self: ScopeMap[k, v], key: k, value: v) Option[v]:
    self.scopes.last().unwrap().insert(key, value)


ScopeMap.get[Hash[k], Eq[k]](self: ScopeMap[k, v], key: k) Option[v]:
    assert(self.scopes.len() > 0)
    let scopeIdx = self.scopes.len() - 1
    loop:
        let scope = self.scopes.get(scopeIdx)
        if scope.get(key) is Option.Some(value):
            return Option.Some(value)
        if scopeIdx == 0:
            break
        scopeIdx -= 1
    Option.None


# ------------------------------------------------------------------------------


impl[ToDoc[k], ToDoc[v]] ToDoc[ScopeMap[k, v]]:
    toDoc(self: ScopeMap[k, v]) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("scopes =")
                + Doc.nested(4, Doc.break_(1) + self.scopes.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ScopeMap") + Doc.char('(') + args)

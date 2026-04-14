use crate::ast::Name;
use crate::collections::ScopeMap;
use crate::type_checker::id::Id;
use crate::type_checker::{ModuleEnv, Ty, TyCon};

/// A map of type constructors, variables, and synonyms in scope.
#[derive(Debug, Default)]
pub struct TyMap {
    /// Module-level type constructors.
    cons: ScopeMap<Id, TyCon>,

    /// Scoped type synonyms (e.g. associated type synonyms within trait/impl blocks). These are
    /// checked first by `resolve`, before looking up in `cons`.
    synonyms: ScopeMap<Name, TyCon>,

    /// Type variables in scope.
    vars: ScopeMap<Name, Ty>,
}

impl TyMap {
    pub fn len_scopes(&self) -> usize {
        self.cons.len_scopes()
    }

    pub fn cons(&self) -> &ScopeMap<Id, TyCon> {
        &self.cons
    }

    pub fn enter_scope(&mut self) {
        self.cons.enter();
        self.synonyms.enter();
        self.vars.enter();
    }

    pub fn exit_scope(&mut self) {
        self.cons.exit();
        self.synonyms.exit();
        self.vars.exit();
    }

    /// Look up a type constructor by name. Checks scoped synonyms first, then resolves via the
    /// module env and looks up in `cons`.
    pub fn resolve(
        &self,
        module_env: &ModuleEnv,
        name: &Name,
        mod_prefix: &Option<crate::module::ModulePath>,
    ) -> Option<&TyCon> {
        // Synonyms are scoped (e.g. associated types), not module-level, so no prefix lookup.
        if mod_prefix.is_none()
            && let Some(syn) = self.synonyms.get(name)
        {
            return Some(syn);
        }
        let id = module_env.get_with_path(name, mod_prefix)?;
        self.cons.get(id)
    }

    pub fn get_con(&self, id: &Id) -> Option<&TyCon> {
        self.cons.get(id)
    }

    pub fn get_con_mut(&mut self, id: &Id) -> Option<&mut TyCon> {
        self.cons.get_mut(id)
    }

    pub fn get_var(&self, id: &Name) -> Option<&Ty> {
        self.vars.get(id)
    }

    pub fn has_con(&self, id: &Id) -> bool {
        self.get_con(id).is_some()
    }

    pub fn insert_var(&mut self, id: Name, ty: Ty) {
        self.vars.insert(id, ty);
    }

    pub fn insert_con(&mut self, id: Id, con: TyCon) {
        self.cons.insert(id, con);
    }

    pub fn insert_synonym(&mut self, name: Name, con: TyCon) {
        self.synonyms.insert(name, con);
    }
}

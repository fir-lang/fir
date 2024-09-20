use crate::ast::Id;
use crate::collections::ScopeMap;
use crate::type_checker::{Ty, TyCon};

/// A map of type constructors and variables in scope.
#[derive(Debug, Default)]
pub struct TyMap {
    cons: ScopeMap<Id, TyCon>,
    vars: ScopeMap<Id, Ty>,
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
        self.vars.enter();
    }

    pub fn exit_scope(&mut self) {
        self.cons.exit();
        self.vars.exit();
    }

    pub fn get_con(&self, id: &Id) -> Option<&TyCon> {
        self.cons.get(id)
    }

    pub fn get_con_mut(&mut self, id: &Id) -> Option<&mut TyCon> {
        self.cons.get_mut(id)
    }

    pub fn get_var(&self, id: &Id) -> Option<&Ty> {
        self.vars.get(id)
    }

    pub fn has_con(&self, id: &Id) -> bool {
        self.get_con(id).is_some()
    }

    #[allow(unused)]
    pub fn has_var(&self, id: &Id) -> bool {
        self.get_var(id).is_some()
    }

    pub fn insert_var(&mut self, id: Id, ty: Ty) {
        self.vars.insert(id, ty);
    }

    pub fn insert_con(&mut self, id: Id, con: TyCon) {
        self.cons.insert(id, con);
    }
}

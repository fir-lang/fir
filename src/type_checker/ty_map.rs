use crate::ast::Id;
use crate::collections::{HashMap, ScopeMap};
use crate::type_checker::{Ty, TyCon};

/// A map of type constructors, variables, and synonyms in scope.
#[derive(Debug, Default)]
pub struct TyMap {
    cons: HashMap<Id, TyCon>,
    vars: ScopeMap<Id, Ty>,
    synonyms: ScopeMap<Id, Ty>,
}

impl TyMap {
    pub fn len_scopes(&self) -> usize {
        self.vars.len_scopes()
    }

    pub fn cons(&self) -> &HashMap<Id, TyCon> {
        &self.cons
    }

    pub fn enter_scope(&mut self) {
        self.vars.enter();
        self.synonyms.enter();
    }

    pub fn exit_scope(&mut self) {
        self.vars.exit();
        self.synonyms.exit();
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

    pub fn get_synonym(&self, id: &Id) -> Option<&Ty> {
        self.synonyms.get(id)
    }

    pub fn has_con(&self, id: &Id) -> bool {
        self.get_con(id).is_some()
    }

    pub fn insert_var(&mut self, id: Id, ty: Ty) {
        self.vars.insert(id, ty);
    }

    pub fn insert_con(&mut self, id: Id, con: TyCon) {
        self.cons.insert(id, con);
    }

    pub fn insert_synonym(&mut self, id: Id, ty: Ty) {
        self.synonyms.insert(id, ty);
    }
}

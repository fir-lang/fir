use crate::ast::Id;
use crate::collections::{Map, ScopeMap};
use crate::type_checker::ty::*;

/// Returns all of the fields in the record including extensions, with extension variable (if
/// exists).
pub(crate) fn collect_record_fields(
    cons: &ScopeMap<Id, TyCon>,
    record_ty: &Ty, // used in errors
    fields: &Map<Id, Ty>,
    mut extension: Option<Box<Ty>>,
) -> (Map<Id, Ty>, Option<Ty>) {
    let mut all_fields: Map<Id, Ty> = fields
        .iter()
        .map(|(id, ty)| (id.clone(), ty.clone()))
        .collect();

    while let Some(ext) = extension {
        match *ext {
            Ty::Record {
                fields,
                extension: next_ext,
            } => {
                for (field_id, field_ty) in fields {
                    if all_fields.insert(field_id, field_ty).is_some() {
                        panic!("BUG: Duplicate field in record {}", record_ty);
                    }
                }
                extension = next_ext;
            }

            Ty::Var(var) => match var.normalize(cons) {
                Ty::Record {
                    fields,
                    extension: next_ext,
                } => {
                    for (field_id, field_ty) in fields {
                        if all_fields.insert(field_id, field_ty).is_some() {
                            panic!("BUG: Duplicate field in record {}", record_ty);
                        }
                    }
                    extension = next_ext;
                }

                other => return (all_fields, Some(other)),
            },

            other => return (all_fields, Some(other)),
        }
    }

    (all_fields, None)
}

/// Similar to `collect_record_fields`, but collects variant constructors.
pub(crate) fn collect_variant_cons(
    cons: &ScopeMap<Id, TyCon>,
    variant_ty: &Ty, // used in errors
    var_cons: &Map<Id, Vec<Ty>>,
    mut extension: Option<Box<Ty>>,
) -> (Map<Id, Vec<Ty>>, Option<Ty>) {
    let mut all_cons: Map<Id, Vec<Ty>> = var_cons.clone();

    while let Some(ext) = extension {
        match *ext {
            Ty::Variant {
                cons,
                extension: next_ext,
            } => {
                for (con, fields) in cons {
                    if all_cons.insert(con, fields).is_some() {
                        panic!("BUG: Duplicate constructor in variant {}", variant_ty);
                    }
                }
                extension = next_ext;
            }

            Ty::Var(var) => match var.normalize(cons) {
                Ty::Variant {
                    cons,
                    extension: next_ext,
                } => {
                    for (con, fields) in cons {
                        if all_cons.insert(con, fields).is_some() {
                            panic!("BUG: Duplicate constructor in variant {}", variant_ty);
                        }
                    }
                    extension = next_ext;
                }

                other => return (all_cons, Some(other)),
            },

            other => return (all_cons, Some(other)),
        }
    }

    (all_cons, None)
}

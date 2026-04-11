use crate::ast::Name;
use crate::collections::*;
use crate::type_checker::id::Id;
use crate::type_checker::traits::TraitEnv;
use crate::type_checker::ty::*;

/// Collect labels and extension of a record type, following record row extensions.
pub(super) fn collect_record_rows(
    cons: &ScopeMap<Id, TyCon>,
    ty: &Ty, // record, used in errors
    labels: &OrdMap<Name, Ty>,
    mut extension: Option<Box<Ty>>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
    assumps: &[Pred],
) -> (OrdMap<Name, Ty>, Option<Ty>) {
    let mut all_labels: OrdMap<Name, Ty> = labels
        .iter()
        .map(|(id, ty)| {
            (
                id.clone(),
                ty.deep_normalize(cons, trait_env, var_gen, assumps),
            )
        })
        .collect();

    while let Some(ext) = extension {
        let normalized = ext.deep_normalize(cons, trait_env, var_gen, assumps);
        let (labels, next_ext, is_row) = match normalized {
            Ty::Record {
                labels,
                extension: next_ext,
                is_row,
            } => (labels, next_ext, is_row),

            Ty::UVar(var) => {
                assert!(
                    matches!(var.kind(), Kind::Row(RecordOrVariant::Record)),
                    "{:?} : {:?}",
                    var,
                    var.kind()
                );
                match var.normalize(cons) {
                    Ty::Record {
                        labels,
                        extension: next_ext,
                        is_row,
                    } => (labels, next_ext, is_row),
                    other => return (all_labels, Some(other)),
                }
            }

            other => return (all_labels, Some(other)),
        };

        assert!(
            is_row,
            "Extension variable in record type is not a row: {ty:#?}"
        );
        for (label_id, label_ty) in labels {
            if all_labels.insert(label_id, label_ty).is_some() {
                panic!("BUG: Duplicate label in record type {ty}");
            }
        }
        extension = next_ext;
    }

    (all_labels, None)
}

/// Collect labels and extension of a variant type, following variant row extensions.
pub(super) fn collect_variant_rows(
    cons: &ScopeMap<Id, TyCon>,
    ty: &Ty, // variant, used in errors
    labels: &OrdMap<Id, Ty>,
    mut extension: Option<Box<Ty>>,
    trait_env: &TraitEnv,
    var_gen: &UVarGen,
    assumps: &[Pred],
) -> (OrdMap<Id, Ty>, Option<Ty>) {
    let mut all_labels: OrdMap<Id, Ty> = labels
        .iter()
        .map(|(id, ty)| {
            (
                id.clone(),
                ty.deep_normalize(cons, trait_env, var_gen, assumps),
            )
        })
        .collect();

    while let Some(ext) = extension {
        let normalized = ext.deep_normalize(cons, trait_env, var_gen, assumps);
        let (labels, next_ext, is_row) = match normalized {
            Ty::Variant {
                labels,
                extension: next_ext,
                is_row,
            } => (labels, next_ext, is_row),

            Ty::UVar(var) => {
                assert!(
                    matches!(var.kind(), Kind::Row(RecordOrVariant::Variant)),
                    "{:?} : {:?}",
                    var,
                    var.kind()
                );
                match var.normalize(cons) {
                    Ty::Variant {
                        labels,
                        extension: next_ext,
                        is_row,
                    } => (labels, next_ext, is_row),
                    other => return (all_labels, Some(other)),
                }
            }

            other => return (all_labels, Some(other)),
        };

        assert!(
            is_row,
            "Extension variable in variant type is not a row: {ty:#?}"
        );
        for (label_id, label_ty) in labels {
            if all_labels.insert(label_id, label_ty).is_some() {
                panic!("BUG: Duplicate label in variant type {ty}");
            }
        }
        extension = next_ext;
    }

    (all_labels, None)
}

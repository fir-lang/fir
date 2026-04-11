use crate::ast::Name;
use crate::collections::*;
use crate::type_checker::traits::TraitEnv;
use crate::type_checker::ty::*;

pub(super) fn collect_rows(
    cons: &ScopeMap<Name, TyCon>,
    ty: &Ty, // record or variant, used in errors
    ty_kind: RecordOrVariant,
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
        let (labels, next_ext, kind, is_row) = match normalized {
            Ty::Record {
                labels,
                extension: next_ext,
                is_row,
            } => (labels, next_ext, RecordOrVariant::Record, is_row),

            Ty::Variant {
                labels,
                extension: next_ext,
                is_row,
            } => (labels, next_ext, RecordOrVariant::Variant, is_row),

            Ty::UVar(var) => {
                assert!(
                    matches!(var.kind(), Kind::Row(_)),
                    "{:?} : {:?}",
                    var,
                    var.kind()
                );
                match var.normalize(cons) {
                    Ty::Record {
                        labels,
                        extension: next_ext,
                        is_row,
                    } => (labels, next_ext, RecordOrVariant::Record, is_row),
                    Ty::Variant {
                        labels,
                        extension: next_ext,
                        is_row,
                    } => (labels, next_ext, RecordOrVariant::Variant, is_row),
                    other => return (all_labels, Some(other)),
                }
            }

            other => return (all_labels, Some(other)),
        };

        assert!(
            is_row,
            "Extension variable in anonymous type is not a row: {ty:#?}"
        );
        assert_eq!(kind, ty_kind);
        for (label_id, label_ty) in labels {
            if all_labels.insert(label_id, label_ty).is_some() {
                panic!("BUG: Duplicate label in anonymous type {ty}");
            }
        }
        extension = next_ext;
    }

    (all_labels, None)
}

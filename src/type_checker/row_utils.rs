use crate::ast::Id;
use crate::collections::*;
use crate::type_checker::ty::*;

pub(crate) fn collect_rows(
    cons: &ScopeMap<Id, TyCon>,
    ty: &Ty, // record or variant, used in errors
    ty_kind: RecordOrVariant,
    labels: &TreeMap<Id, Ty>,
    mut extension: Option<Box<Ty>>,
) -> (TreeMap<Id, Ty>, Option<Ty>) {
    let mut all_labels: TreeMap<Id, Ty> = labels
        .iter()
        .map(|(id, ty)| (id.clone(), ty.deep_normalize(cons)))
        .collect();

    while let Some(ext) = extension {
        match *ext {
            Ty::Anonymous {
                labels,
                extension: next_ext,
                kind,
                is_row,
            } => {
                assert_eq!(kind, ty_kind);
                assert!(is_row);
                for (label_id, label_ty) in labels {
                    if all_labels.insert(label_id, label_ty).is_some() {
                        panic!("BUG: Duplicate label in anonymous type {}", ty);
                    }
                }
                extension = next_ext;
            }

            Ty::Var(var) => {
                assert!(
                    matches!(var.kind(), Kind::Row(_)),
                    "{:?} : {:?}",
                    var,
                    var.kind()
                );
                match var.normalize(cons) {
                    Ty::Anonymous {
                        labels,
                        extension: next_ext,
                        kind,
                        is_row,
                    } => {
                        assert!(
                            is_row,
                            "Extension variable in anonymous type is not a row: {:#?}",
                            ty
                        );
                        assert_eq!(kind, ty_kind);
                        for (label_id, label_ty) in labels {
                            if all_labels.insert(label_id, label_ty).is_some() {
                                panic!("BUG: Duplicate field in anonymous type {}", ty);
                            }
                        }
                        extension = next_ext;
                    }

                    other => return (all_labels, Some(other)),
                }
            }

            other => return (all_labels, Some(other)),
        }
    }

    (all_labels, None)
}

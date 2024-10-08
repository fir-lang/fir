use crate::ast::{self, Id};
use crate::type_checker::unification::unify;
use crate::type_checker::*;

pub(crate) fn apply(
    ty: &Ty,
    args: &Vec<ast::Named<Ty>>,
    cons: &ScopeMap<Id, TyCon>,
    loc: &ast::Loc,
) -> Ty {
    match ty {
        Ty::Fun(ty_args, ty_ret) => {
            assert_eq!(ty_args.len(), args.len());
            for (ty1, ty2) in ty_args.iter().zip(args.iter()) {
                assert!(ty2.name.is_none());
                unify(ty1, &ty2.node, cons, loc);
            }
            (**ty_ret).clone()
        }

        Ty::FunNamedArgs(ty_args, ty_ret) => {
            assert_eq!(ty_args.len(), args.len());

            for ast::Named { name, node } in args {
                let name = name.as_ref().unwrap();
                let ty1 = ty_args.get(name).unwrap();
                unify(ty1, node, cons, loc);
            }

            (**ty_ret).clone()
        }

        Ty::Con(_)
        | Ty::Var(_)
        | Ty::App(_, _)
        | Ty::Record(_)
        | Ty::QVar(_)
        | Ty::AssocTySelect { .. } => {
            if args.is_empty() {
                return ty.clone();
            }
            panic!("ty = {:?}, args = {:?}", ty, args)
        }
    }
}

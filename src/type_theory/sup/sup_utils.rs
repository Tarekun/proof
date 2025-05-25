use super::sup::SupFormula::{self, ForAll};

pub fn get_arg_types(forall: &SupFormula) -> Vec<SupFormula> {
    match forall {
        ForAll(_, var_type, body) => {
            let mut result = vec![*var_type.clone()];
            let rest = get_arg_types(&body);
            result.extend(rest);
            result
        }
        _ => vec![],
    }
}

pub fn get_forall_innermost(forall: &SupFormula) -> SupFormula {
    match forall {
        ForAll(_, _, body) => get_forall_innermost(&body),
        _ => forall.to_owned(),
    }
}

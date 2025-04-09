use crate::type_theory::commons::utils::generic_multiarg_fun_type;

use super::fol::{Fol, FolType, FolType::Arrow};

pub fn make_multiarg_fun_type(
    arg_types: &[(String, FolType)],
    base: &FolType,
) -> FolType {
    generic_multiarg_fun_type::<Fol, _>(
        arg_types,
        base,
        |_, arg_type, sub_type| Arrow(Box::new(arg_type), Box::new(sub_type)),
    )
}

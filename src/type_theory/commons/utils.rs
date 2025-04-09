use crate::type_theory::interface::TypeTheory;

pub fn generic_multiarg_fun_type<T, F>(
    arg_types: &[(String, T::Type)],
    base: &T::Type,
    aggregator: F,
) -> T::Type
where
    T: TypeTheory,
    F: Fn(String, T::Type, T::Type) -> T::Type + Copy,
{
    if arg_types.is_empty() {
        return base.to_owned();
    }

    let ((arg_name, arg_type), rest) = arg_types.split_first().unwrap();
    let sub_type = generic_multiarg_fun_type::<T, F>(rest, base, aggregator);

    aggregator(arg_name.to_owned(), arg_type.to_owned(), sub_type)
}

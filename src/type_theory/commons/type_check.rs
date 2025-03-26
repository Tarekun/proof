use crate::type_theory::{environment::Environment, interface::TypeTheory};

/// Generic variable type checking. Implements the classic VAR type checking
/// rule of checking x:T ∈ Γ, where x is `var_name`, T the returned type, and
/// Γ the `environment`
pub fn generic_type_check_variable<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    var_name: &str,
) -> Result<T::Type, String> {
    match environment.get_variable_type(var_name) {
        Some(var_type) => Ok(var_type),
        None => Err(format!("Unbound variable: {}", var_name)),
    }
}

/// Generic abstraction type checking. Implements classic ABS type checking
/// rule of Γ ⊢ λa:A.b : A->B, where a is `var_name`, A is `var_type`, b is
/// `body`, and B is the returned type.
/// Creating the functional type A->B is left to type theories implementations
pub fn generic_type_check_abstraction<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    var_name: &str,
    var_type: &T::Type,
    body: &T::Term,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(var_type, environment)?;
    environment.with_local_declaration(var_name, var_type, |local_env| {
        let body_type = T::type_check_term(body, local_env)?;
        Ok(body_type)
    })
}

// pub fn type_check_application<T: TypeTheory>(
//     environment: &mut Environment<T::Term, T::Type>,
//     left: T::Term,
//     right: T::Term,
// ) -> Result<T::Type, String> {
//     fn type_check_nested_app<T: TypeTheory>(
//         local_env: &mut Environment<T::Term, T::Type>,
//         term: T::Term,
//     ) -> Result<T::Type, String> {
//         match term {
//             // idncutive case:
//             Application(left, right) => {
//                 let function_type =
//                     type_check_nested_app(local_env, *left.clone())?;
//                 let arg_type = T::type_check_term(*right.clone(), local_env)?;

//                 match function_type.clone() {
//                     T::Term::Function(var_name, domain, codomain) => {
//                         if T::types_unify(local_env, domain, &arg_type) {
//                             local_env.add_variable_definition(&var_name, &right, &arg_type);
//                             // δ-reduce the body type in case its dependent on var_name
//                             match delta_reduce(local_env, *codomain.clone()) {
//                                 Ok(body) => Ok(body),
//                                 _ => Ok(*codomain)
//                             }
//                         } else {
//                             Err(format!(
//                                 "Function and argument have uncompatible types: function expects a {:?} but the argument has type {:?}",
//                                 *domain,
//                                 arg_type
//                             ))
//                         }
//                     }
//                     _ => Err(format!(
//                         "Attempted application on non functional term '{:?}' of type: {:?}",
//                         left,
//                         function_type
//                     )),
//                 }
//             }
//             // base case: type check the fuction (leftmost term)
//             _ => {
//                 let term_type = T::type_check_term(term, local_env)?;
//                 Ok(term_type)
//             }
//         }
//     }

//     environment.with_rollback(|local_env| {
//         type_check_nested_app(
//             local_env,
//             Application(Box::new(left), Box::new(right)),
//         )
//     })
// }

use crate::{
    misc::Union,
    misc::Union::{L, R},
    parser::api::Tactic,
    type_theory::{environment::Environment, interface::TypeTheory},
};

use super::evaluation::{
    generic_evaluate_axiom, generic_evaluate_fun, generic_evaluate_let,
    generic_evaluate_theorem,
};

//########################### EXPRESSIONS TYPE CHECKING
//
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

/// Generic universal quantification type checking. Implements first order
/// universal quantification Γ ⊢ ∀a:A.P(a), where a is `var_name`, A is
/// `var_type`, and P(a) is a dependent `predicate`.
/// Creating the dependent type Πa:A.P a is left to type theories implementations
pub fn generic_type_check_universal<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    var_name: &str,
    var_type: &T::Type,
    predicate: &T::Type,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(var_type, environment)?;
    environment.with_local_declaration(var_name, var_type, |local_env| {
        let body_type = T::type_check_type(predicate, local_env)?;
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
//########################### EXPRESSIONS TYPE CHECKING
//
//########################### STATEMENTS TYPE CHECKING
//
/// Generic let definition type checking. Uses `T::type_check_type` on the variable type
pub fn generic_type_check_let<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    var_name: &str,
    opt_type: &Option<T::Type>,
    body: &T::Term,
) -> Result<T::Type, String> {
    let body_type = T::type_check_term(body, environment)?;
    let var_type = if opt_type.is_none() {
        body_type.to_owned()
    } else {
        opt_type.to_owned().unwrap()
    };
    let _ = T::type_check_type(&var_type, environment)?;

    if T::types_unify(environment, &var_type, &body_type) {
        generic_evaluate_let::<T>(environment, var_name, &Some(var_type), body);
        Ok(body_type)
    } else {
        Err(format!(
            "Error in variable {} definition: declared type {:?} and assigned {:?} do not unify",
            var_name,
            var_type,
            var_type
        ))
    }
}

/// Generic function definition type checking
pub fn generic_type_check_fun<
    T: TypeTheory,
    F: Fn(&[(String, T::Type)], &T::Type) -> T::Type,
>(
    environment: &mut Environment<T::Term, T::Type>,
    fun_name: &str,
    args: &Vec<(String, T::Type)>,
    out_type: &T::Type,
    body: &T::Term,
    is_rec: &bool,
    make_fun_type: F,
) -> Result<T::Type, String> {
    let fun_type = make_fun_type(&args, &out_type);
    let _ = T::type_check_type(&fun_type, environment);
    let mut assumptions = args.to_owned();
    if *is_rec {
        assumptions.push((fun_name.to_string(), fun_type.clone()));
        //TODO possibly include necessary checks on recursive functions
    }

    let body_type = environment
        .with_local_declarations(&assumptions, |local_env| {
            T::type_check_term(&body, local_env)
        })?;
    if !T::types_unify(environment, out_type, &body_type) {
        return Err(format!(
            "In {} definition, function type {:?} and body result {:?} are inconsistent",
            fun_name, out_type, body_type
        ));
    }

    generic_evaluate_fun::<T, _>(
        environment,
        fun_name,
        args,
        out_type,
        body,
        is_rec,
        make_fun_type,
    );
    Ok(fun_type)
}

/// Geneirc axiom type checking. Uses `T::type_check_type` on `predicate` and
/// updates the environment with the axiom
pub fn generic_type_check_axiom<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    axiom_name: &str,
    predicate: &T::Type,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(predicate, environment)?;
    generic_evaluate_axiom::<T>(environment, axiom_name, predicate);

    Ok(predicate.to_owned())
}

/// Generic theorem type checking. If `proof` is a term style proof it type checks
/// the body and checks unification with the theorem `formula`;
pub fn generic_type_check_theorem<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    theorem_name: &str,
    formula: &T::Type,
    proof: &Union<T::Term, Vec<Tactic>>,
) -> Result<T::Type, String> {
    let _ = T::type_check_type(formula, environment)?;
    match proof {
        L(proof_term) => {
            let proof_type = T::type_check_term(proof_term, environment)?;
            if !T::types_unify(environment, &formula, &proof_type) {
                return Err(format!(
                    "Proof term's type doesn't unify with the theorem statement. Expected {:?} but found {:?}",
                    formula, proof_type
                ));
            }
            generic_evaluate_theorem::<T>(
                environment,
                theorem_name,
                formula,
                proof,
            );
            Ok(formula.to_owned())
        }
        R(interactive_proof) => {
            //TODO
            Ok(formula.to_owned())
        }
    }
}
//########################### STATEMENTS TYPE CHECKING

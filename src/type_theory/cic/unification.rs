use super::cic::CicTerm;
use super::cic::CicTerm::Variable;
use crate::type_theory::environment::Environment;

pub fn cic_unification(
    environment: &mut Environment<CicTerm, CicTerm>,
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<bool, String> {
    let are_alpha_equivalent = alpha_equivalent(environment, term1, term2)?;
    let are_equal_under_substitutions =
        equal_under_substitution(environment, term1, term2);

    Ok(are_alpha_equivalent || are_equal_under_substitutions)
}

//TODO support pattern matching equivalence
pub fn alpha_equivalent(
    environment: &mut Environment<CicTerm, CicTerm>,
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<bool, String> {
    match term1 {
        // if both variable they must have matching types
        CicTerm::Variable(_) => match term2 {
            CicTerm::Variable(_) => {
                // let type1 = Cic::type_check_term(term1.clone(), environment)?;
                // let type2 = Cic::type_check_term(term2.clone(), environment)?;
                // Ok(type1 == type2)
                // alpha_equivalent(environment, &type1, &type2)
                Ok(equal_under_substitution(environment, term1, term2)) //TODO is this the real right logic here?
            }
            _ => Ok(false),
        },
        // if both abstration they must have matching types for inputs/outputs
        CicTerm::Abstraction(_, arg1, res1) => match term2 {
            CicTerm::Abstraction(_, arg2, res2) => {
                let args_unify = alpha_equivalent(environment, arg1, arg2)?;
                let res_unify = alpha_equivalent(environment, res1, res2)?;

                Ok(args_unify && res_unify)
            }
            _ => Ok(false),
        },
        // if both products they must have matching types for inputs/outputs
        CicTerm::Product(_, arg1, res1) => match term2 {
            CicTerm::Product(_, arg2, res2) => {
                let args_unify = alpha_equivalent(environment, arg1, arg2)?;
                let res_unify = alpha_equivalent(environment, res1, res2)?;

                Ok(args_unify && res_unify)
            }
            _ => Ok(false),
        },
        // if both applications they must have matching types for function and input
        CicTerm::Application(fun1, arg1) => match term2 {
            CicTerm::Application(fun2, arg2) => {
                let funs_unify = alpha_equivalent(environment, fun1, fun2)?;
                let arg_unify = alpha_equivalent(environment, arg1, arg2)?;

                Ok(funs_unify && arg_unify)
            }
            _ => Ok(false),
        },
        // default case: sorts must be equal
        _ => Ok(equal_under_substitution(environment, term1, term2)),
    }
}

pub fn equal_under_substitution(
    environment: &mut Environment<CicTerm, CicTerm>,
    term1: &CicTerm,
    term2: &CicTerm,
) -> bool {
    fn check_var_subst(
        environment: &mut Environment<CicTerm, CicTerm>,
        variable: &CicTerm,
        fixed_term: &CicTerm,
    ) -> bool {
        match variable {
            Variable(var_name) => {
                if let Some((_, (body, _))) =
                    environment.get_from_deltas(&var_name)
                {
                    variable == fixed_term || body == fixed_term
                } else {
                    variable == fixed_term
                }
            }
            _ => variable == fixed_term,
        }
    }

    check_var_subst(environment, term1, term2)
        || check_var_subst(environment, term2, term1)
}

#[cfg(test)]
mod unit_tests {
    use crate::type_theory::cic::{
        cic::{
            Cic,
            CicTerm::{Abstraction, Product, Sort, Variable},
        },
        unification::{
            alpha_equivalent, cic_unification, equal_under_substitution,
        },
    };
    use crate::type_theory::interface::TypeTheory;

    #[test]
    fn test_alpha_eqivalence() {
        let mut test_env = Cic::default_environment();
        test_env.add_variable_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_variable_to_context("Bool", &Sort("TYPE".to_string()));

        assert_eq!(
            alpha_equivalent(
                &mut test_env,
                &Sort("PROP".to_string()),
                &Sort("PROP".to_string()),
            ),
            Ok(true),
            "Alpha equivalence refuses equal sorts"
        );
        assert_eq!(
            alpha_equivalent(
                &mut test_env,
                &Sort("TYPE".to_string()),
                &Sort("PROP".to_string()),
            ),
            Ok(false),
            "Alpha equivalence accepts different sorts"
        );
        assert_eq!(
            alpha_equivalent(
                &mut test_env,
                &Abstraction(
                    "x".to_string(),
                    Box::new(Sort("PROP".to_string())),
                    Box::new(Sort("TYPE".to_string()))
                ),
                &Abstraction(
                    "y".to_string(),
                    Box::new(Sort("PROP".to_string())),
                    Box::new(Sort("TYPE".to_string()))
                )
            ),
            Ok(true),
            "Alpha equivalence refuses equivalent abstractions"
        );
        assert_eq!(
            alpha_equivalent(
                &mut test_env,
                &Product(
                    "x".to_string(),
                    Box::new(Sort("PROP".to_string())),
                    Box::new(Sort("TYPE".to_string()))
                ),
                &Product(
                    "y".to_string(),
                    Box::new(Sort("PROP".to_string())),
                    Box::new(Sort("PROP".to_string()))
                )
            ),
            Ok(false),
            "Alpha equivalence accepts non-equivalent abstractions"
        );
        assert_eq!(
            alpha_equivalent(
                &mut test_env,
                &Variable("Nat".to_string()),
                &Variable("Bool".to_string()),
            ),
            Ok(false),
            "Alpha equivalence accepts different types as equivalent"
        );
    }

    #[test]
    fn test_substitution() {
        let mut test_env = Cic::default_environment();
        test_env.add_variable_definition(
            "T",
            &Variable("Bool".to_string()),
            &Sort("TYPE".to_string()),
        );

        assert!(
            equal_under_substitution(
                &mut test_env,
                &Variable("T".to_string()),
                &Variable("Bool".to_string())
            ),
            "Equality up2 substitution refutes basic substitution check"
        );
    }

    #[test]
    fn test_aplha_with_substitution() {
        let mut test_env = Cic::default_environment();
        test_env.add_variable_definition(
            "T",
            &Variable("Nat".to_string()),
            &Sort("TYPE".to_string()),
        );

        assert_eq!(
            cic_unification(
                &mut test_env,
                &Product(
                    "_".to_string(),
                    Box::new(Variable("Unit".to_string())),
                    Box::new(Variable("T".to_string())),
                ),
                &Product(
                    "x".to_string(),
                    Box::new(Variable("Unit".to_string())),
                    Box::new(Variable("Nat".to_string())),
                ),
            ),
            Ok(true),
            "Equality up2 substitution refutes substitution check over codomains of functions"
        );

        assert!(
            Cic::terms_unify(
                &mut test_env,
                &Product(
                    "_".to_string(),
                    Box::new(Variable("Unit".to_string())),
                    Box::new(Variable("T".to_string())),
                ),
                &Product(
                    "x".to_string(),
                    Box::new(Variable("Unit".to_string())),
                    Box::new(Variable("Nat".to_string())),
                ),
            ),
            "Equality up2 substitution refutes substitution check over codomains of functions"
        );
    }
}

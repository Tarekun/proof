use super::cic::{Cic, CicTerm};
use crate::type_theory::{
    cic::cic::make_default_environment, environment::Environment,
    interface::TypeTheory,
};

//TODO support pattern matching equivalence
pub fn alpha_equivalent(
    environment: &mut Environment<CicTerm, CicTerm>,
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<bool, String> {
    println!("Confronting {:?} and {:?}", term1, term2);
    match term1 {
        // if both variable they must have matching types
        CicTerm::Variable(_) => match term2 {
            CicTerm::Variable(_) => {
                // let type1 = Cic::type_check_term(term1.clone(), environment)?;
                // let type2 = Cic::type_check_term(term2.clone(), environment)?;
                // Ok(type1 == type2)
                // alpha_equivalent(environment, &type1, &type2)
                Ok(term1 == term2) //TODO is this the real right logic here?
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
        _ => Ok(term1 == term2),
    }
}

#[test]
fn test_alpha_eqivalence() {
    let mut test_env = make_default_environment();

    assert_eq!(
        alpha_equivalent(
            &mut test_env,
            &CicTerm::Sort("PROP".to_string()),
            &CicTerm::Sort("PROP".to_string()),
        ),
        Ok(true),
        "Alpha equivalence refuses equal sorts"
    );
    assert_eq!(
        alpha_equivalent(
            &mut test_env,
            &CicTerm::Sort("TYPE".to_string()),
            &CicTerm::Sort("PROP".to_string()),
        ),
        Ok(false),
        "Alpha equivalence accepts different sorts"
    );
    assert_eq!(
        alpha_equivalent(
            &mut test_env,
            &CicTerm::Abstraction(
                "x".to_string(),
                Box::new(CicTerm::Sort("PROP".to_string())),
                Box::new(CicTerm::Sort("TYPE".to_string()))
            ),
            &CicTerm::Abstraction(
                "y".to_string(),
                Box::new(CicTerm::Sort("PROP".to_string())),
                Box::new(CicTerm::Sort("TYPE".to_string()))
            )
        ),
        Ok(true),
        "Alpha equivalence refuses equivalent abstractions"
    );
    assert_eq!(
        alpha_equivalent(
            &mut test_env,
            &CicTerm::Product(
                "x".to_string(),
                Box::new(CicTerm::Sort("PROP".to_string())),
                Box::new(CicTerm::Sort("TYPE".to_string()))
            ),
            &CicTerm::Product(
                "y".to_string(),
                Box::new(CicTerm::Sort("PROP".to_string())),
                Box::new(CicTerm::Sort("PROP".to_string()))
            )
        ),
        Ok(false),
        "Alpha equivalence accepts non-equivalent abstractions"
    );
}

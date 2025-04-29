use super::cic::CicTerm;
use super::cic::CicTerm::{
    Abstraction, Application, Match, Meta, Product, Sort, Variable,
};
use crate::misc::simple_map;
use crate::type_theory::environment::Environment;
use std::collections::{HashMap, VecDeque};

fn substitute_meta(term: &CicTerm, target: &i32, arg: &CicTerm) -> CicTerm {
    match term {
        Meta(index) => {
            if index == target {
                arg.clone()
            } else {
                term.clone()
            }
        }
        Sort(_) => term.clone(),
        Variable(_) => term.clone(),
        Application(left, right) => Application(
            Box::new(substitute_meta(left, target, arg)),
            Box::new(substitute_meta(right, target, arg)),
        ),
        // TODO: dont carry substitution if names match to implement overriding of names
        Abstraction(var_name, domain, codomain) => Abstraction(
            var_name.to_string(),
            Box::new(substitute_meta(domain, target, arg)),
            Box::new(substitute_meta(codomain, target, arg)),
        ),
        Product(var_name, domain, codomain) => Product(
            var_name.to_string(),
            Box::new(substitute_meta(domain, target, arg)),
            Box::new(substitute_meta(codomain, target, arg)),
        ),
        Match(matched_term, branches) => Match(
            Box::new(substitute_meta(matched_term, target, arg)),
            //TODO i dont want to clone branches here tbh
            simple_map(branches.clone(), |(pattern, body)| {
                (
                    simple_map(pattern, |term| {
                        substitute_meta(&term, target, arg)
                    }),
                    substitute_meta(&body, target, arg),
                )
            }),
        ),
    }
}

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

pub fn solve_unification(
    constraints: Vec<(CicTerm, CicTerm)>,
) -> Result<HashMap<i32, CicTerm>, String> {
    fn occurs_check(meta_index: i32, term: &CicTerm) -> Result<(), String> {
        match term {
            Meta(index) => {
                if meta_index == *index {
                    Err("Unification Failure: cyclical metavariable reference"
                        .to_string())
                } else {
                    Ok(())
                }
            }
            Abstraction(_, arg_type, body) => {
                occurs_check(meta_index, arg_type)?;
                occurs_check(meta_index, body)
            }
            Product(_, arg_type, body) => {
                occurs_check(meta_index, arg_type)?;
                occurs_check(meta_index, body)
            }
            Application(left, right) => {
                occurs_check(meta_index, &left)?;
                occurs_check(meta_index, &right)
            }
            Match(matched, branches) => {
                for (pattern, body) in branches {
                    for term in pattern {
                        occurs_check(meta_index, term)?;
                    }
                    occurs_check(meta_index, body)?;
                }
                occurs_check(meta_index, &matched)
            }
            _ => Ok(()),
        }
    }

    fn handle_meta(
        index: i32,
        term: &CicTerm,
        substitution: HashMap<i32, CicTerm>,
    ) -> Result<HashMap<i32, CicTerm>, String> {
        if let Meta(_) = term {
            return Err("TF am i supposed todo with this?".to_string());
        }
        occurs_check(index, &term)?;

        // this update introduces a quadratic cost in the overall algo
        let mut substitution: HashMap<i32, CicTerm> = substitution
            .iter()
            .map(|(k, v)| (*k, substitute_meta(v, &index, &term)))
            .collect();
        substitution.insert(index, term.clone());
        Ok(substitution)
    }

    fn missmatch_error(
        left: &CicTerm,
        right: &CicTerm,
    ) -> Result<HashMap<i32, CicTerm>, String> {
        Err(format!(
            "Unification failed: {:?} and {:?} don't unify",
            left, right
        ))
    }

    fn solver(
        mut constraints: VecDeque<(CicTerm, CicTerm)>,
        substitution: HashMap<i32, CicTerm>,
    ) -> Result<HashMap<i32, CicTerm>, String> {
        match constraints.len() {
            0 => Ok(substitution),
            _ => {
                let (left, right) = constraints.pop_front().unwrap();
                let error_obj = missmatch_error(&left, &right);
                match (left, right) {
                    (Meta(index), right) => solver(
                        constraints,
                        handle_meta(index, &right, substitution)?,
                    ),
                    (left, Meta(index)) => solver(
                        constraints,
                        handle_meta(index, &left, substitution)?,
                    ),
                    (Variable(left_name), Variable(right_name)) => {
                        if left_name != right_name {
                            //TODO im not totally sure this is necessary
                            return missmatch_error(
                                &Variable(left_name),
                                &Variable(right_name),
                            );
                        } else {
                            solver(constraints, substitution)
                        }
                    }
                    (Sort(left_sort), Sort(right_sort)) => {
                        //TODO support universes/subtypes
                        if left_sort != right_sort {
                            return missmatch_error(
                                &Sort(left_sort),
                                &Sort(right_sort),
                            );
                        } else {
                            solver(constraints, substitution)
                        }
                    }
                    (
                        Abstraction(_, left_arg_type, left_body),
                        Abstraction(_, right_arg_type, right_body),
                    ) => {
                        //TODO add eta reduction like in matita?
                        constraints
                            .push_back((*left_arg_type, *right_arg_type));
                        constraints.push_back((*left_body, *right_body));
                        solver(constraints, substitution)
                    }
                    (
                        Product(_, left_arg_type, left_body),
                        Product(_, right_arg_type, right_body),
                    ) => {
                        constraints
                            .push_back((*left_arg_type, *right_arg_type));
                        constraints.push_back((*left_body, *right_body));
                        solver(constraints, substitution)
                    }
                    (
                        Application(left_fun, left_arg),
                        Application(right_fun, right_arg),
                    ) => {
                        constraints.push_back((*left_fun, *right_fun));
                        constraints.push_back((*left_arg, *right_arg));
                        solver(constraints, substitution)
                    }
                    (
                        Match(left_matched_term, left_branches),
                        Match(right_matched_term, right_branches),
                    ) => {
                        constraints.push_back((
                            (*left_matched_term).clone(),
                            (*right_matched_term).clone(),
                        ));

                        // if left_branches.len() != right_branches.len() {
                        //     return missmatch_error(left, right);
                        // }
                        // for (
                        //     (left_pattern, left_body),
                        //     (right_pattern, right_body),
                        // ) in left_branches.iter().zip(right_branches)
                        // {
                        //     constraints.push_back((
                        //         left_pattern.clone(),
                        //         right_pattern.clone(),
                        //     ));
                        //     constraints.push_back((
                        //         (*left_body).clone(),
                        //         (*right_body).clone(),
                        //     ));
                        // }

                        solver(constraints, substitution)
                    }
                    _ => error_obj,
                }
            }
        }
    }

    solver(constraints.into_iter().collect(), HashMap::new())
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
                if let Some((_, body)) = environment.get_from_deltas(&var_name)
                {
                    variable == fixed_term || body == *fixed_term
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
            CicTerm::{Abstraction, Meta, Product, Sort, Variable},
        },
        unification::{
            alpha_equivalent, cic_unification, equal_under_substitution,
            solve_unification,
        },
    };
    use crate::type_theory::interface::TypeTheory;
    use std::collections::HashMap;

    #[test]
    fn test_dhm() {
        let constraints = vec![(Meta(0), Variable("Nat".to_string()))];
        let expected = {
            let mut map = HashMap::new();
            map.insert(0, Variable("Nat".to_string()));
            map
        };
        assert_eq!(
            solve_unification(constraints).unwrap(),
            expected,
            "Unification couldnt solve one simple constraint"
        );

        let constraints = vec![
            (
                Meta(1),
                Product(
                    "_".to_string(),
                    Box::new(Variable("Nat".to_string())),
                    Box::new(Meta(0)),
                ),
            ),
            (Meta(0), Variable("Unit".to_string())),
        ];
        let expected = {
            let mut map = HashMap::new();
            map.insert(0, Variable("Unit".to_string()));
            map.insert(
                1,
                Product(
                    "_".to_string(),
                    Box::new(Variable("Nat".to_string())),
                    Box::new(Variable("Unit".to_string())),
                ),
            );
            map
        };
        assert_eq!(
            solve_unification(constraints).unwrap(),
            expected,
            "Unification couldnt solve one simple constraint"
        );
    }

    #[test]
    fn test_structurally_equal_terms() {}

    #[test]
    fn test_alpha_eqivalence() {
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("Bool", &Sort("TYPE".to_string()));

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
        test_env.add_substitution_with_type(
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
        test_env.add_substitution_with_type(
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

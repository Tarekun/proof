use core::panic;

use super::cic::CicStm::{Axiom, Fun, InductiveDef, Let, Theorem};
use super::cic::CicTerm::{
    Abstraction, Application, Match, Product, Sort, Variable,
};
use super::cic::{Cic, CicStm, CicTerm};
use super::cic_utils::make_multiarg_fun_type;
use crate::misc::{
    simple_map, Union,
    Union::{L, R},
};
use crate::parser::api::Tactic;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

//########################### TERM βδ-REDUCTION
pub fn reduce_term(
    environment: &mut Environment<CicTerm, CicTerm>,
    term: &CicTerm,
) -> CicTerm {
    match term {
        Variable(var_name) => reduce_variable(environment, term, var_name),
        Application(left, right) => {
            reduce_application(environment, left, right)
        }
        Match(matched_term, branches) => {
            reduce_match(environment, matched_term, branches)
        }
        _ => term.clone(),
    }
}
//
//
fn reduce_variable(
    environment: &Environment<CicTerm, CicTerm>,
    og_term: &CicTerm,
    var_name: &str,
) -> CicTerm {
    // if a substitution exists the variable δ-reduces to its definition
    if let Some((_, (body, _))) = environment.get_from_deltas(var_name) {
        body.clone()
    }
    // otherwise it's a constant, ie a value
    else {
        og_term.clone()
    }
}
//
//
fn reduce_application(
    environment: &mut Environment<CicTerm, CicTerm>,
    left: &CicTerm,
    right: &CicTerm,
) -> CicTerm {
    if let Ok(fun_type) = Cic::type_check_term(left.clone(), environment) {
        match fun_type {
            Product(var_name, _, _) => {
                // if left is function variable take its body, otherwise gets left back
                let left_body = reduce_term(environment, left);
                // TODO do i substitute right or do i substitute its reduction? big deal
                let right_reduced = reduce_term(environment, right);
                substitute(&left_body, &var_name, &right_reduced)
            }
            _ => {
                panic!(
                    "Trying to reduce an application of term {:?} that doesn't have a functional type. This should have been caught sooner", 
                    left
                );
            }
        }
    } else {
        panic!(
            "Trying to reduce an application of term {:?} that is ill-typed. This should have been caught sooner",
            left
        );
    }
}
//
//
fn reduce_match(
    environment: &mut Environment<CicTerm, CicTerm>,
    matched_term: &CicTerm,
    branches: &Vec<(Vec<CicTerm>, CicTerm)>,
) -> CicTerm {
    // let normalized_term = reduce_term(environment, matched_term);
    // for (pattern, body) in branches {
    //     if matches_pattern(normalized_term, pattern) {

    //     }
    // }

    panic!(
        "No pattern matched the term {:?}, if this is a type checking or exhaustiveness error, it should have been caught sooner",
        matched_term
    );
}
//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn evaluate_statement(
    environment: &mut Environment<CicTerm, CicTerm>,
    stm: &CicStm,
) -> () {
    match stm {
        Axiom(axiom_name, formula) => {
            evaluate_axiom(environment, axiom_name, formula)
        }
        Let(var_name, var_type, body) => {
            evaluate_let(environment, var_name, var_type, body)
        }
        Fun(fun_name, args, out_type, body, is_rec) => {
            evaluate_fun(environment, fun_name, args, out_type, body, *is_rec)
        }
        Theorem(theorem_name, formula, proof) => {
            evaluate_theorem(environment, theorem_name, formula, proof)
        }
        _ => (),
    }
}
//
//
pub fn evaluate_axiom(
    environment: &mut Environment<CicTerm, CicTerm>,
    axiom_name: &str,
    formula: &CicTerm,
) -> () {
    environment.add_variable_to_context(axiom_name, formula);
}
//
//
pub fn evaluate_let(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: &str,
    var_type: &Option<CicTerm>,
    body: &CicTerm,
) -> () {
    let var_type = match var_type {
        Some(type_term) => type_term,
        None => {
            let body_type = Cic::type_check_term(body.clone(), environment);
            if body_type.is_err() {
                panic!("Evaluating a let definition with ill type body, this should have been caught sooner");
            }
            &body_type.unwrap()
        }
    };
    environment.add_variable_definition(var_name, body, var_type);
}
//
//
pub fn evaluate_fun(
    environment: &mut Environment<CicTerm, CicTerm>,
    fun_name: &str,
    args: &Vec<(String, CicTerm)>,
    out_type: &CicTerm,
    body: &CicTerm,
    _is_rec: bool,
) -> () {
    let fun_type = make_multiarg_fun_type(&args, out_type);
    environment.add_variable_definition(fun_name, body, &fun_type);
}
//
//
pub fn evaluate_theorem(
    environment: &mut Environment<CicTerm, CicTerm>,
    theorem_name: &str,
    formula: &CicTerm,
    proof: &Union<CicTerm, Vec<Tactic>>,
) -> () {
    match proof {
        L(_proof_term) => {
            environment.add_variable_to_context(&theorem_name, &formula);
        }
        //TODO support itp
        R(interactive_proof) => {}
    }
}
//########################### STATEMENTS EXECUTION
//
//########################### HELPER FUNCTIONS
// fn is_reducable(
//     environment: &Environment<CicTerm, CicTerm>,
//     term: CicTerm,
// ) -> bool {
//     match term {
//         Application(_, _) => true,
//         Match(_, _) => true,
//         Variable(var_name) => match environment.get_from_deltas(&var_name) {
//             Some(_) => true,
//             None => false,
//         },
//         _ => false,
//     }
// }

/// Given a `term` and a variable, returns a term where each instance of
/// `var_name` is substituted with `arg`
fn substitute(term: &CicTerm, target_name: &str, arg: &CicTerm) -> CicTerm {
    match term {
        Sort(_) => term.clone(),
        Variable(var_name) => {
            if var_name == target_name {
                arg.clone()
            } else {
                term.clone()
            }
        }
        Application(left, right) => Application(
            Box::new(substitute(left, target_name, arg)),
            Box::new(substitute(right, target_name, arg)),
        ),
        Abstraction(var_name, domain, codomain) => Abstraction(
            var_name.to_string(),
            Box::new(substitute(domain, target_name, arg)),
            Box::new(substitute(codomain, target_name, arg)),
        ),
        Product(var_name, domain, codomain) => Product(
            var_name.to_string(),
            Box::new(substitute(domain, target_name, arg)),
            Box::new(substitute(codomain, target_name, arg)),
        ),
        Match(matched_term, branches) => Match(
            Box::new(substitute(matched_term, target_name, arg)),
            //TODO i dont want to clone branches here tbh
            simple_map(branches.clone(), |(pattern, body)| {
                (
                    simple_map(pattern, |term| {
                        substitute(&term, target_name.clone(), arg)
                    }),
                    substitute(&body, target_name, arg),
                )
            }),
        ),
    }
}
//########################### HELPER FUNCTIONS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::{
        cic::{
            cic::{
                Cic,
                CicTerm::{
                    Abstraction, Application, Match, Product, Sort, Variable,
                },
            },
            evaluation::{evaluate_let, reduce_application, reduce_variable},
        },
        interface::TypeTheory,
    };

    #[test]
    fn test_var_reduction() {
        let mut test_env = Cic::default_environment();
        test_env.add_variable_definition(
            "test",
            &Variable("Unit".to_string()),
            &Sort("TYPE".to_string()),
        );

        assert_eq!(
            reduce_variable(
                &test_env,
                &Variable("constant".to_string()),
                "constant"
            ),
            Variable("constant".to_string()),
            "Constant δ-reduces to something other than itself"
        );
        assert_eq!(
            reduce_variable(&test_env, &Variable("test".to_string()), "test"),
            Variable("Unit".to_string()),
            "Defined variable doesnt δ-reduce to its body"
        );
    }

    #[test]
    fn test_app_reduction() {
        let mut test_env = Cic::default_environment();
        test_env.add_variable_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_variable_to_context(
            "s",
            &Product(
                "".to_string(),
                Box::new(Variable("Nat".to_string())),
                Box::new(Variable("Nat".to_string())),
            ),
        );
        test_env.add_variable_definition(
            "add_one",
            &Application(
                Box::new(Variable("s".to_string())),
                Box::new(Variable("n".to_string())),
            ),
            &Product(
                "n".to_string(),
                Box::new(Variable("Nat".to_string())),
                Box::new(Variable("Nat".to_string())),
            ),
        );

        assert_eq!(
            reduce_application(
                &mut test_env,
                &Variable("add_one".to_string()),
                &Variable("arg".to_string())
            ),
            Application(
                Box::new(Variable("s".to_string())),
                Box::new(Variable("arg".to_string())),
            ),
            "Function application doesnt reduce to the function body with substituted variable"
        );
    }
}

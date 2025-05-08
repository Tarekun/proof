use core::panic;

use super::cic::CicStm::{Axiom, Fun, Let, Theorem};
use super::cic::CicTerm::{
    Abstraction, Application, Match, Meta, Product, Sort, Variable,
};
use super::cic::{Cic, CicStm, CicTerm};
use super::cic_utils::{make_multiarg_fun_type, substitute};
use crate::misc::{simple_map, Union};
use crate::parser::api::Tactic;
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function,
};
use crate::type_theory::commons::evaluation::{
    generic_evaluate_axiom, generic_evaluate_fun, generic_evaluate_let,
    generic_evaluate_theorem, generic_reduce_variable,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

//########################### TERM βδ-REDUCTION
pub fn one_step_reduction(
    environment: &mut Environment<CicTerm, CicTerm>,
    term: &CicTerm,
) -> CicTerm {
    match term {
        Variable(var_name) => reduce_variable(environment, var_name, term),
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
    var_name: &str,
    og_term: &CicTerm,
) -> CicTerm {
    generic_reduce_variable::<Cic>(environment, var_name, og_term)
}
//
/// Given a functional term returns its body if it has one defined, or None if
/// it doesnt exist. Assumes that function variables are already β-reduced
fn get_body(reduced_function: &CicTerm) -> Option<CicTerm> {
    match reduced_function {
        Abstraction(_, _, body) => Some(*body.clone()),
        _ => None,
    }
}
fn reduce_application(
    environment: &mut Environment<CicTerm, CicTerm>,
    left: &CicTerm,
    right: &CicTerm,
) -> CicTerm {
    if let Ok(fun_type) = Cic::type_check_term(&left, environment) {
        match fun_type {
            Product(var_name, _, _) => {
                // if left is function variable take its body, otherwise gets left back
                let left_reduced = Cic::normalize_term(environment, left);
                // TODO do i substitute right or do i substitute its reduction? big deal
                let right_reduced = Cic::normalize_term(environment, right);

                match get_body(&left_reduced) {
                    Some(body) => substitute(&body, &var_name, &right_reduced),
                    None => Application(
                        Box::new(left_reduced),
                        Box::new(right_reduced),
                    ),
                }
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
    let normalized_term = Cic::normalize_term(environment, matched_term);
    for (pattern, body) in branches {
        if matches_pattern(&normalized_term, pattern) {
            return body.clone();
        }
    }

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
            evaluate_fun(environment, fun_name, args, out_type, body, is_rec)
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
    generic_evaluate_axiom::<Cic>(environment, axiom_name, formula);
}
//
//
pub fn evaluate_let(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: &str,
    var_type: &Option<CicTerm>,
    body: &CicTerm,
) -> () {
    generic_evaluate_let::<Cic>(environment, var_name, var_type, body);
}
//
//
pub fn evaluate_fun(
    environment: &mut Environment<CicTerm, CicTerm>,
    fun_name: &str,
    args: &Vec<(String, CicTerm)>,
    out_type: &CicTerm,
    body: &CicTerm,
    is_rec: &bool,
) -> () {
    generic_evaluate_fun::<Cic, _>(
        environment,
        fun_name,
        args,
        out_type,
        body,
        is_rec,
        make_multiarg_fun_type,
    );
}
//
//
pub fn evaluate_theorem(
    environment: &mut Environment<CicTerm, CicTerm>,
    theorem_name: &str,
    formula: &CicTerm,
    proof: &Union<CicTerm, Vec<Tactic>>,
) -> () {
    generic_evaluate_theorem::<Cic>(environment, theorem_name, formula, proof);
}
//########################### STATEMENTS EXECUTION
//
//########################### HELPER FUNCTIONS
/// Given a `term` and a `pattern`, returns `true` if the term matches the
/// pattern, `false` otherwise
fn matches_pattern(term: &CicTerm, pattern: &Vec<CicTerm>) -> bool {
    let outermost = get_applied_function(term);
    let args = application_args(term.to_owned());

    // TODO i think this should match the types as well but im not sure
    return (outermost == pattern[0]) && (args.len() == pattern.len() - 1);
}
//########################### HELPER FUNCTIONS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::{
        cic::{
            cic::{
                Cic,
                CicTerm::{Abstraction, Application, Product, Sort, Variable},
            },
            evaluation::{
                matches_pattern, reduce_application, reduce_match,
                reduce_variable,
            },
        },
        interface::TypeTheory,
    };

    #[test]
    fn test_check_pattern_matching() {
        assert!(
            matches_pattern(
                &Variable("z".to_string()),
                &vec![Variable("z".to_string())]
            ),
            "Pattern matching refutes identical constants"
        );
        assert!(
            !matches_pattern(
                &Variable("z".to_string()),
                &vec![Variable("s".to_string())]
            ),
            "Pattern matching accepts different constants"
        );
        assert!(
            matches_pattern(
                &Application(
                    Box::new(Variable("s".to_string())),
                    Box::new(Variable("z".to_string())),
                ),
                &vec![
                    Variable("s".to_string()),
                    Variable("renamed_argument".to_string()),
                ]
            ),
            "Pattern matching refutes application with renamed argument"
        );
        assert!(
            !matches_pattern(
                &Application(
                    Box::new(Application(
                        Box::new(Variable("cons".to_string())),
                        Box::new(Variable("z".to_string())),
                    )),
                    Box::new(Variable("l".to_string()))
                ),
                &vec![Variable("cons".to_string()), Variable("z".to_string()),]
            ),
            "Pattern matching accepts only partial pattern"
        );
    }

    #[test]
    fn test_var_reduction() {
        let mut test_env = Cic::default_environment();
        test_env.add_substitution_with_type(
            "test",
            &Variable("Unit".to_string()),
            &Sort("TYPE".to_string()),
        );

        assert_eq!(
            reduce_variable(
                &test_env,
                "constant",
                &Variable("constant".to_string()),
            ),
            Variable("constant".to_string()),
            "Constant δ-reduces to something other than itself"
        );
        assert_eq!(
            reduce_variable(&test_env, "test", &Variable("test".to_string())),
            Variable("Unit".to_string()),
            "Defined variable doesnt δ-reduce to its body"
        );
    }

    #[test]
    fn test_app_reduction() {
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("z", &Variable("Nat".to_string()));
        test_env.add_to_context(
            "s",
            &Product(
                "".to_string(),
                Box::new(Variable("Nat".to_string())),
                Box::new(Variable("Nat".to_string())),
            ),
        );
        test_env.add_substitution_with_type(
            "add_one",
            &Abstraction(
                "n".to_string(),
                Box::new(Variable("Nat".to_string())),
                Box::new(Application(
                    Box::new(Variable("s".to_string())),
                    Box::new(Variable("n".to_string())),
                )),
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
                &Variable("s".to_string()),
                &Variable("z".to_string())
            ),
            Application(
                Box::new(Variable("s".to_string())),
                Box::new(Variable("z".to_string())),
            ),
            "Function application of normal form returns a different term"
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

    #[test]
    fn test_match_reduction() {
        let mut test_env = Cic::default_environment();
        let zero = Variable("z".to_string());
        let succ_pattern =
            vec![Variable("s".to_string()), Variable("n".to_string())];
        let true_term = Variable("true".to_string());
        let false_term = Variable("false".to_string());

        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("z", &Variable("Nat".to_string()));
        test_env.add_to_context(
            "s",
            &Product(
                "_".to_string(),
                Box::new(Variable("Nat".to_string())),
                Box::new(Variable("Nat".to_string())),
            ),
        );
        test_env.add_substitution_with_type(
            "x",
            &zero,
            &Variable("Nat".to_string()),
        );

        assert_eq!(
            reduce_match(
                &mut test_env,
                &zero,
                &vec![
                    (vec![zero.clone()], true_term.clone()),
                    (succ_pattern.clone(), false_term.clone())
                ]
            ),
            true_term,
            "Match term doesnt δ-reduce to the right branch body"
        );
        assert_eq!(
            reduce_match(
                &mut test_env,
                &Variable("x".to_string()),
                &vec![
                    (vec![zero.clone()], true_term.clone()),
                    (succ_pattern.clone(), false_term.clone())
                ]
            ),
            true_term,
            "Match term doesnt δ-reduce if matching a variable that needs reduction"
        );
        assert_eq!(
            reduce_match(
                &mut test_env,
                &Application(
                    Box::new(Variable("s".to_string())),
                    Box::new(Variable("z".to_string()))
                ),
                &vec![
                    (vec![zero.clone()], true_term.clone()),
                    (succ_pattern.clone(), false_term.clone())
                ]
            ),
            false_term,
            "Match term doesnt δ-reduce if matching an application pattern"
        );
    }
}

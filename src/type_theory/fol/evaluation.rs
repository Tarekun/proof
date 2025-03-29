use crate::{
    misc::Union,
    parser::api::Tactic,
    type_theory::{
        commons::evaluation::{
            generic_evaluate_axiom, generic_evaluate_let,
            generic_evaluate_theorem, generic_reduce_variable,
        },
        environment::Environment,
    },
};

use super::fol::{Fol, FolStm, FolTerm, FolType};

//########################### TERM βδ-REDUCTION
pub fn reduce_term(
    environment: &mut Environment<FolTerm, FolType>,
    term: &FolTerm,
) -> FolTerm {
    term.clone()
}
//
//
fn reduce_variable(
    environment: &Environment<FolTerm, FolType>,
    var_name: &str,
    og_term: &FolTerm,
) -> FolTerm {
    generic_reduce_variable::<Fol>(environment, var_name, og_term)
}

//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn evaluate_statement(
    environment: &mut Environment<FolTerm, FolType>,
    stm: &FolStm,
) -> () {
    ()
}
//
//
pub fn evaluate_let(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: &str,
    var_type: &Option<FolType>,
    body: &FolTerm,
) -> () {
    generic_evaluate_let::<Fol>(environment, var_name, var_type, body);
}
//
//
pub fn evaluate_axiom(
    environment: &mut Environment<FolTerm, FolType>,
    axiom_name: &str,
    formula: &FolType,
) -> () {
    generic_evaluate_axiom::<Fol>(environment, axiom_name, formula);
}
//
//
pub fn evaluate_theorem(
    environment: &mut Environment<FolTerm, FolType>,
    theorem_name: &str,
    formula: &FolType,
    proof: &Union<FolTerm, Vec<Tactic>>,
) -> () {
    generic_evaluate_theorem::<Fol>(environment, theorem_name, formula, proof);
}
//########################### STATEMENTS EXECUTION
//
//########################### HELPER FUNCTIONS
//########################### HELPER FUNCTIONS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {}

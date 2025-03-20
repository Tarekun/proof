use crate::type_theory::environment::Environment;

use super::fol::{FolStm, FolTerm, FolType};

//########################### TERM βδ-REDUCTION
pub fn reduce_term(
    environment: &mut Environment<FolTerm, FolType>,
    term: &FolTerm,
) -> FolTerm {
    term.clone()
}

//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn evaluate_statement(
    environment: &mut Environment<FolTerm, FolType>,
    stm: &FolStm,
) -> () {
    ()
}
//########################### STATEMENTS EXECUTION
//
//########################### HELPER FUNCTIONS
//########################### HELPER FUNCTIONS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {}

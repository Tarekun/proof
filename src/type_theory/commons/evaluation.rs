use crate::{
    misc::Union,
    misc::Union::{L, R},
    parser::api::Tactic,
    type_theory::{environment::Environment, interface::TypeTheory},
};

//########################### TERM βδ-REDUCTION
pub fn generic_reduce_variable<T: TypeTheory>(
    environment: &Environment<T::Term, T::Type>,
    var_name: &str,
    og_term: &T::Term,
) -> T::Term {
    // if a substitution exists the variable δ-reduces to its definition
    if let Some((_, (body, _))) = environment.get_from_deltas(var_name) {
        body.to_owned()
    }
    // otherwise it's a constant, ie a value
    else {
        og_term.to_owned()
    }
}
//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn generic_evaluate_let<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    var_name: &str,
    var_type: &Option<T::Type>,
    body: &T::Term,
) -> () {
    let var_type: &T::Type = match var_type {
        Some(type_term) => type_term,
        None => {
            let body_type = T::type_check_term(&body, environment);
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
pub fn generic_evaluate_axiom<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    axiom_name: &str,
    formula: &T::Type,
) -> () {
    environment.add_variable_to_context(axiom_name, formula);
}
//
//
pub fn generic_evaluate_theorem<T: TypeTheory>(
    environment: &mut Environment<T::Term, T::Type>,
    theorem_name: &str,
    formula: &T::Type,
    proof: &Union<T::Term, Vec<Tactic>>,
) -> () {
    match proof {
        L(_proof_term) => {
            environment.add_variable_to_context(&theorem_name, &formula);
        }
        //TODO support itp
        R(_interactive_proof) => {}
    }
}
//########################### STATEMENTS EXECUTION

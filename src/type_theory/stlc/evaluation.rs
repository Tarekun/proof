use super::stlc::{Stlc, StlcTerm, StlcType};
use crate::parsing::NsAst;
use crate::type_theory::interface::TypeTheory;
use crate::{parsing::Expression, type_theory::environment::Environment};

fn cast_to_type(
    env: &Environment<StlcTerm, StlcType>,
    term_type: StlcTerm,
) -> StlcType {
    match term_type {
        StlcTerm::Variable(var_name) => match env.get_atomic_type(&var_name) {
            Some((_, type_obj)) => type_obj.clone(),
            None => panic!("Unbound type: {}", var_name),
        },
        _ => {
            panic!("Non variable term used in place of a type: {:?}", term_type)
        }
    }
}

//########################### EXPRESSIONS EVALUATION
pub fn evaluate_var(
    environment: &Environment<StlcTerm, StlcType>,
    var_name: String,
) -> (StlcTerm, StlcType) {
    match environment.get_from_deltas(&var_name) {
        Some((var_name, (_, term_type))) => {
            (StlcTerm::Variable(var_name.to_string()), term_type.clone())
        }
        None => match environment.get_from_context(&var_name) {
            Some((var_name, term_type)) => {
                (StlcTerm::Variable(var_name.to_string()), term_type.clone())
            }
            None => match environment.get_atomic_type(&var_name) {
                Some((var_name, term_obj)) => {
                    (StlcTerm::Variable(var_name.to_string()), term_obj.clone())
                }
                None => panic!("Unbound variable: {}", var_name),
            },
        },
    }
}

pub fn evaluate_abstraction(
    environment: &mut Environment<StlcTerm, StlcType>,
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> (StlcTerm, StlcType) {
    let (var_type_term, _) = Stlc::evaluate_expression(var_type, environment);
    let var_type = cast_to_type(&environment, var_type_term);
    //TODO update the context only temporarily, during body evaluation
    environment.add_variable_to_context(&var_name, &var_type);
    let (body_term, body_type) = Stlc::evaluate_expression(body, environment);

    let function = StlcTerm::Abstraction(
        var_name.clone(),
        Box::new(var_type.clone()),
        Box::new(body_term),
    );

    (
        function,
        StlcType::Arrow(Box::new(var_type), Box::new(body_type)),
    )
}

pub fn evaluate_application(
    environment: &mut Environment<StlcTerm, StlcType>,
    left: Expression,
    right: Expression,
) -> (StlcTerm, StlcType) {
    let (left_term, left_type) = Stlc::evaluate_expression(left, environment);
    let (right_term, _) = Stlc::evaluate_expression(right, environment);

    match left_type {
        StlcType::Arrow(_, codomain) => (
            StlcTerm::Application(Box::new(left_term), Box::new(right_term)),
            *codomain,
        ),
        _ => panic!("Cannot apply an atomic type"),
    }
}

pub fn evaluate_let(
    environment: &mut Environment<StlcTerm, StlcType>,
    var_name: String,
    ast: Expression,
) -> (StlcTerm, StlcType) {
    let (assigned_term, term_type) =
        Stlc::evaluate_expression(ast, environment);
    environment.add_variable_definition(&var_name, &assigned_term, &term_type);

    (StlcTerm::Variable(var_name), term_type)
}
//########################### EXPRESSIONS EVALUATION

//########################### STATEMENTS EVALUATION
pub fn evaluate_file_root(
    environment: &mut Environment<StlcTerm, StlcType>,
    _file_path: String,
    asts: Vec<NsAst>,
) {
    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(stm) => {
                Stlc::evaluate_statement(stm, environment);
            }
            NsAst::Exp(exp) => {
                let _ = Stlc::evaluate_expression(exp, environment);
            }
        }
    }
}
//########################### STATEMENTS EVALUATION

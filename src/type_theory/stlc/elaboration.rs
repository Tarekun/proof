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
pub fn elaborate_var(var_name: String) -> StlcTerm {
    StlcTerm::Variable(var_name)
}

pub fn elaborate_abstraction(
    environment: &mut Environment<StlcTerm, StlcType>,
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> StlcTerm {
    let var_type_term = Stlc::elaborate_expression(var_type);
    let var_type = cast_to_type(&environment, var_type_term);
    let body_term = Stlc::elaborate_expression(body);

    StlcTerm::Abstraction(
        var_name.clone(),
        Box::new(var_type.clone()),
        Box::new(body_term),
    )
}

pub fn elaborate_application(left: Expression, right: Expression) -> StlcTerm {
    let left_term = Stlc::elaborate_expression(left);
    let right_term = Stlc::elaborate_expression(right);

    StlcTerm::Application(Box::new(left_term), Box::new(right_term))
}

pub fn elaborate_let(
    environment: &mut Environment<StlcTerm, StlcType>,
    var_name: String,
    ast: Expression,
) {
    let assigned_term = Stlc::elaborate_expression(ast);
    match Stlc::type_check(assigned_term.clone(), environment) {
        Ok(assigned_type) => {
            environment.add_variable_definition(
                &var_name,
                &assigned_term,
                &assigned_type,
            );
        }
        Err(_) => panic!("ill-typed body in variable definition"),
    }
}
//########################### EXPRESSIONS EVALUATION

//########################### STATEMENTS EVALUATION
pub fn elaborate_file_root(
    environment: &mut Environment<StlcTerm, StlcType>,
    _file_path: String,
    asts: Vec<NsAst>,
) {
    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(stm) => {
                Stlc::elaborate_statement(stm, environment);
            }
            NsAst::Exp(exp) => {
                let _ = Stlc::elaborate_expression(exp);
            }
        }
    }
}
//########################### STATEMENTS EVALUATION

use super::stlc::{Stlc, StlcTerm, StlcType};
use crate::{
    parser::api::{Expression, NsAst},
    type_theory::{environment::Environment, interface::TypeTheory},
};

fn cast_to_type(term_type: &StlcTerm) -> StlcType {
    match term_type {
        StlcTerm::Variable(var_name) => StlcType::Atomic(var_name.clone()),
        StlcTerm::ArrowTmpTerm(domain, codomain) => {
            let domain_type = cast_to_type(&domain);
            let codomain_type = cast_to_type(&codomain);

            StlcType::Arrow(Box::new(domain_type), Box::new(codomain_type))
        }
        _ => {
            panic!("Non variable term used in place of a type: {:?}", term_type)
        }
    }
}

//########################### EXPRESSIONS ELABORATION
pub fn elaborate_var_use(var_name: String) -> StlcTerm {
    StlcTerm::Variable(var_name)
}

pub fn elaborate_abstraction(
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> StlcTerm {
    let var_type_term = Stlc::elaborate_expression(var_type);
    let var_type = cast_to_type(&var_type_term);
    let body_term = Stlc::elaborate_expression(body);

    StlcTerm::Abstraction(
        var_name.clone(),
        Box::new(var_type),
        Box::new(body_term),
    )
}

pub fn elaborate_arrow(domain: Expression, codomain: Expression) -> StlcTerm {
    let domain_term = Stlc::elaborate_expression(domain);
    let codomain_term = Stlc::elaborate_expression(codomain);

    //TODO this shit ugly af, elaboration should probably return a union typ
    //of terms and types to avoid this bs
    StlcTerm::ArrowTmpTerm(Box::new(domain_term), Box::new(codomain_term))
}

pub fn elaborate_application(left: Expression, right: Expression) -> StlcTerm {
    let left_term = Stlc::elaborate_expression(left);
    let right_term = Stlc::elaborate_expression(right);

    StlcTerm::Application(Box::new(left_term), Box::new(right_term))
}

pub fn elaborate_let(
    environment: &mut Environment<StlcTerm, StlcType>,
    var_name: String,
    var_type: Expression,
    var_body: Expression,
) {
    let assigned_term = Stlc::elaborate_expression(var_body);
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
//########################### EXPRESSIONS ELABORATION

//########################### STATEMENTS ELABORATION
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
//########################### STATEMENTS ELABORATION

//########################### UNIT TESTS

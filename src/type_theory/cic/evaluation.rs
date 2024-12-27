use super::cic::SystemFTerm;
use crate::parsing::NsAst;
use crate::type_theory::interface::TypeTheory;
use crate::{
    parsing::Expression,
    type_theory::{cic::cic::Cic, environment::Environment},
};

fn make_functional_type(
    domain: SystemFTerm,
    codomain: SystemFTerm,
) -> SystemFTerm {
    SystemFTerm::Product("_".to_string(), Box::new(domain), Box::new(codomain))
}

//########################### EXPRESSIONS EVALUATION
pub fn evaluate_var(
    environment: &Environment<SystemFTerm, SystemFTerm>,
    var_name: &str,
) -> (SystemFTerm, SystemFTerm) {
    match environment.get_from_deltas(&var_name) {
        //TODO should delta-reduce the variable here?
        Some((var_name, (_, var_type))) => (
            SystemFTerm::Variable(var_name.to_string()),
            var_type.clone(),
        ),

        None => match environment.get_from_context(&var_name) {
            Some((var_name, var_type)) => (
                SystemFTerm::Variable(var_name.to_string()),
                var_type.clone(),
            ),
            None => panic!("Unbound variable: {}", var_name),
        },
    }
}

pub fn evaluate_abstraction(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> (SystemFTerm, SystemFTerm) {
    let (var_type_term, _) = Cic::evaluate_expression(var_type, environment);
    //TODO update the context only temporarily, during body evaluation
    environment.add_variable_to_context(&var_name, &var_type_term);
    let (body_term, body_type) = Cic::evaluate_expression(body, environment);

    let function = SystemFTerm::Abstraction(
        var_name.clone(),
        Box::new(var_type_term.clone()),
        Box::new(body_term),
    );

    (function, make_functional_type(var_type_term, body_type))
}

pub fn evaluate_type_product(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> (SystemFTerm, SystemFTerm) {
    let (type_term, _) = Cic::evaluate_expression(var_type, environment);
    //TODO update the context only temporarily, during body evaluation
    environment.add_variable_to_context(&var_name, &type_term);
    let (body_term, _) = Cic::evaluate_expression(body, environment);

    let dependent_type = SystemFTerm::Product(
        var_name.clone(),
        Box::new(type_term),
        Box::new(body_term),
    );

    (dependent_type, SystemFTerm::Sort("TYPE".to_string()))
}

pub fn evaluate_application(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    left: Expression,
    right: Expression,
) -> (SystemFTerm, SystemFTerm) {
    let (left_term, function_type) =
        Cic::evaluate_expression(left, environment);
    let (right_term, _) = Cic::evaluate_expression(right, environment);

    match function_type {
        SystemFTerm::Product(_, _, codomain) => (
            SystemFTerm::Application(Box::new(left_term), Box::new(right_term)),
            *codomain, //TODO: how do i handle dependent types?
        ),
        SystemFTerm::Sort(_) => {
            match left_term.clone() {
                SystemFTerm::Product(_, _, codomain) => (
                    SystemFTerm::Application(
                        Box::new(left_term),
                        Box::new(right_term),
                    ),
                    *codomain, //TODO: how do i handle dependent types?
                ),
                _ => panic!(
                "application of a non functional term TF?! term {:?} : {:?}",
                left_term,
                function_type
            ),
            }
        }
        _ => panic!(
            "application of a non functional term TF?! term {:?} : {:?}",
            left_term, function_type
        ),
    }
}

pub fn evaluate_let(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    var_name: String,
    body: Expression,
) -> (SystemFTerm, SystemFTerm) {
    let (assigned_term, term_type) =
        Cic::evaluate_expression(body, environment);

    environment.add_variable_definition(&var_name, &assigned_term, &term_type);

    (SystemFTerm::Variable(var_name), term_type)
}
//########################### EXPRESSIONS EVALUATION

//########################### STATEMENTS EVALUATION
pub fn evaluate_inductive(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    type_name: String,
    constructors: Vec<(String, Vec<Expression>)>,
) {
    fn make_constr_type(
        arguments: &[SystemFTerm],
        base: SystemFTerm,
    ) -> SystemFTerm {
        if arguments.is_empty() {
            return base;
        }

        let (arg, rest) = arguments.split_first().unwrap();
        let sub_type = make_constr_type(rest, base);

        SystemFTerm::Product(
            "_".to_string(),
            Box::new(arg.to_owned()),
            Box::new(sub_type),
        )
    }

    for (constr_name, arg_types) in constructors {
        let mut arg_term_types = vec![];
        for arg_type_exp in arg_types {
            let (arg_type, _) =
                Cic::evaluate_expression(arg_type_exp, environment);
            arg_term_types.push(arg_type);
        }

        let constr_type = make_constr_type(
            &arg_term_types,
            SystemFTerm::Variable(type_name.clone()),
        );
        environment.add_variable_to_context(&constr_name, &constr_type);
    }

    environment.add_variable_to_context(
        &type_name,
        &SystemFTerm::Sort("TYPE".to_string()),
    );
}

pub fn evaluate_file_root(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    _file_path: String,
    asts: Vec<NsAst>,
) {
    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(stm) => Cic::evaluate_statement(stm, environment),
            NsAst::Exp(exp) => {
                let (_, _) = Cic::evaluate_expression(exp, environment);
            }
        }
    }
}

pub fn evaluate_axiom(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    axiom_name: String,
    ast: Expression,
) {
    let (axiom_term, axiom_type) = Cic::evaluate_expression(ast, environment);
    //TODO should also add axiom_term : axiom_type ?
    environment.add_variable_to_context(&axiom_name, &axiom_term);
}
//########################### STATEMENTS EVALUATION

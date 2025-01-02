use super::cic::CicTerm;
use crate::parsing::NsAst;
use crate::type_theory::interface::TypeTheory;
use crate::{
    parsing::Expression,
    type_theory::{cic::cic::Cic, environment::Environment},
};

//########################### EXPRESSIONS EVALUATION
pub fn elaborate_var_use(var_name: String) -> CicTerm {
    if var_name.chars().all(|c| c.is_ascii_uppercase()) {
        CicTerm::Sort(var_name)
    } else {
        CicTerm::Variable(var_name)
    }
}

pub fn elaborate_abstraction(
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> CicTerm {
    let var_type_term = Cic::elaborate_expression(var_type);
    let body_term = Cic::elaborate_expression(body);

    CicTerm::Abstraction(
        var_name.clone(),
        Box::new(var_type_term.clone()),
        Box::new(body_term),
    )
}

pub fn elaborate_type_product(
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> CicTerm {
    let type_term = Cic::elaborate_expression(var_type);
    let body_term = Cic::elaborate_expression(body);

    CicTerm::Product(var_name.clone(), Box::new(type_term), Box::new(body_term))
}

pub fn elaborate_application(left: Expression, right: Expression) -> CicTerm {
    let left_term = Cic::elaborate_expression(left);
    let right_term = Cic::elaborate_expression(right);

    CicTerm::Application(Box::new(left_term), Box::new(right_term))
}

pub fn elaborate_match(
    matched_exp: Expression,
    branches: Vec<(Vec<Expression>, Expression)>,
) -> CicTerm {
    let matched_term = Cic::elaborate_expression(matched_exp);

    let mut branch_terms = vec![];
    for (pattern, body_exp) in branches {
        //TODO i dont like having to clone arg
        let constr_term = Cic::elaborate_expression(pattern[0].clone());
        let mut pattern_terms = vec![constr_term];
        for arg in &pattern[1..] {
            let arg_term = Cic::elaborate_expression(arg.clone());

            //clone is inexpensive as this is either a (atomic) variable or crashes
            match arg_term.clone() {
                CicTerm::Variable(_) => {
                    pattern_terms.push(arg_term);
                }
                _ => panic!("Argument expression should be just a variable"),
            }
        }

        let body_term = Cic::elaborate_expression(body_exp);

        branch_terms.push((pattern_terms, body_term));
    }

    CicTerm::Match(Box::new(matched_term), branch_terms)
}
//########################### EXPRESSIONS EVALUATION

//########################### STATEMENTS EVALUATION
pub fn elaborate_let(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
    var_type: Expression,
    body: Expression,
) {
    let assigned_term = Cic::elaborate_expression(body);
    let var_type_term = Cic::elaborate_expression(var_type);

    match Cic::type_check(assigned_term.clone(), environment) {
        Ok(assigned_type) => {
            if assigned_type == var_type_term {
                environment.add_variable_definition(
                    &var_name,
                    &assigned_term,
                    &assigned_type,
                );
            } else {
                panic!(
                    "Missmatch in variable and body types: specified body type is {:?} but body has type {:?}",
                    var_type_term, assigned_type
                );
            }
        }
        Err(_) => panic!("ill-typed body in variable definition"),
    }
}

pub fn elaborate_inductive(
    environment: &mut Environment<CicTerm, CicTerm>,
    type_name: String,
    constructors: Vec<(String, Vec<Expression>)>,
) {
    fn make_constr_type(arguments: &[CicTerm], base: CicTerm) -> CicTerm {
        if arguments.is_empty() {
            return base;
        }

        let (arg, rest) = arguments.split_first().unwrap();
        let sub_type = make_constr_type(rest, base);

        CicTerm::Product(
            "_".to_string(),
            Box::new(arg.to_owned()),
            Box::new(sub_type),
        )
    }

    for (constr_name, arg_types) in constructors {
        let mut arg_term_types = vec![];
        for arg_type_exp in arg_types {
            let arg_type = Cic::elaborate_expression(arg_type_exp);
            arg_term_types.push(arg_type);
        }

        let constr_type = make_constr_type(
            &arg_term_types,
            CicTerm::Variable(type_name.clone()),
        );
        environment.add_variable_to_context(&constr_name, &constr_type);
    }

    environment.add_variable_to_context(
        &type_name,
        //TODO support selecting the sort TYPE/PROP
        &CicTerm::Sort("TYPE".to_string()),
    );
}

pub fn elaborate_file_root(
    environment: &mut Environment<CicTerm, CicTerm>,
    _file_path: String,
    asts: Vec<NsAst>,
) {
    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(stm) => Cic::elaborate_statement(stm, environment),
            NsAst::Exp(exp) => {
                let _ = Cic::elaborate_expression(exp);
            }
        }
    }
}

pub fn elaborate_axiom(
    environment: &mut Environment<CicTerm, CicTerm>,
    axiom_name: String,
    ast: Expression,
) {
    let axiom_forumla = Cic::elaborate_expression(ast);
    environment.add_variable_to_context(&axiom_name, &axiom_forumla);
}
//########################### STATEMENTS EVALUATION

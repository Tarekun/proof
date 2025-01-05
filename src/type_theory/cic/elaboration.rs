use super::cic::CicTerm;
use crate::parser::api::{Expression, NsAst};
use crate::type_theory::interface::TypeTheory;
use crate::type_theory::{cic::cic::Cic, environment::Environment};

fn make_multiarg_fun_type(
    arg_types: &[(String, CicTerm)],
    base: CicTerm,
) -> CicTerm {
    if arg_types.is_empty() {
        return base;
    }

    let ((arg_name, arg_type), rest) = arg_types.split_first().unwrap();
    let sub_type = make_multiarg_fun_type(rest, base);

    CicTerm::Product(
        arg_name.to_string(),
        Box::new(arg_type.to_owned()),
        Box::new(sub_type),
    )
}

//########################### EXPRESSIONS ELABORATION
pub fn elaborate_var_use(var_name: String) -> CicTerm {
    //TODO this should probably be at the parser level
    if var_name.len() > 1 && var_name.chars().all(|c| c.is_ascii_uppercase()) {
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
//########################### EXPRESSIONS ELABORATION

//########################### STATEMENTS ELABORATION
pub fn elaborate_let(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
    var_type: Expression,
    body: Expression,
) {
    let assigned_term = Cic::elaborate_expression(body);
    //TODO perform type checking
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

//TODO perform type checking
pub fn elaborate_inductive(
    environment: &mut Environment<CicTerm, CicTerm>,
    type_name: String,
    parameters: Vec<(String, Expression)>,
    ariety: Expression,
    constructors: Vec<(String, Vec<(String, Expression)>)>,
) {
    fn map_args_to_terms(
        expressions: Vec<(String, Expression)>,
    ) -> Vec<(String, CicTerm)> {
        let mut arg_types = vec![];
        for (arg_name, arg_type_exp) in expressions {
            let arg_type = Cic::elaborate_expression(arg_type_exp);
            arg_types.push((arg_name, arg_type));
        }

        arg_types
    }

    fn build_inductive_target(
        params: &[(String, CicTerm)],
        base: CicTerm,
    ) -> CicTerm {
        if params.is_empty() {
            return base;
        }

        let ((param_name, _param_type), rest) = params.split_first().unwrap();
        build_inductive_target(
            rest,
            CicTerm::Application(
                Box::new(base),
                Box::new(CicTerm::Variable(param_name.to_string())),
            ),
        )
    }

    let params_types = map_args_to_terms(parameters);
    let ariety_term = Cic::elaborate_expression(ariety);
    let ind_base = build_inductive_target(
        &params_types,
        CicTerm::Variable(type_name.clone()),
    );

    for (constr_name, args) in constructors {
        let arg_types = map_args_to_terms(args);
        let constr_base_type =
            make_multiarg_fun_type(&arg_types, ind_base.clone());
        let constr_full_type =
            make_multiarg_fun_type(&params_types, constr_base_type);

        environment.add_variable_to_context(&constr_name, &constr_full_type);
    }

    match Cic::type_check(ariety_term.clone(), environment) {
        Ok(_) => environment.add_variable_to_context(
            &type_name,
            &make_multiarg_fun_type(&params_types, ariety_term),
        ),
        Err(_) => panic!("TODO"),
    }
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

//TODO perform type checking (axiom_forumla should be PROP)
pub fn elaborate_axiom(
    environment: &mut Environment<CicTerm, CicTerm>,
    axiom_name: String,
    ast: Expression,
) {
    let axiom_forumla = Cic::elaborate_expression(ast);
    environment.add_variable_to_context(&axiom_name, &axiom_forumla);
}
//########################### STATEMENTS ELABORATION

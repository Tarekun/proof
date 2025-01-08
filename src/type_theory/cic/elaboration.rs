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

pub fn elaborate_inductive(
    type_name: String,
    parameters: Vec<(String, Expression)>,
    ariety: Expression,
    constructors: Vec<(String, Vec<(String, Expression)>)>,
) -> CicTerm {
    let parameter_terms: Vec<(String, CicTerm)> = parameters
        .iter()
        .map(|(var_name, var_type)| {
            (
                var_name.to_owned(),
                Cic::elaborate_expression(var_type.to_owned()),
            )
        })
        .collect();
    let ariety_term: CicTerm = Cic::elaborate_expression(ariety);
    let constructor_terms: Vec<(String, Vec<(String, CicTerm)>)> = constructors
        .iter()
        .map(|(constr_name, arguments)| {
            (
                constr_name.to_owned(),
                arguments
                    .iter()
                    .map(|(arg_name, arg_type)| {
                        (
                            arg_name.to_owned(),
                            Cic::elaborate_expression(arg_type.to_owned()),
                        )
                    })
                    .collect(),
            )
        })
        .collect();

    CicTerm::InductiveDef(
        type_name,
        parameter_terms,
        Box::new(ariety_term),
        constructor_terms,
    )
    // fn map_args_to_terms(
    //     expressions: Vec<(String, Expression)>,
    // ) -> Vec<(String, CicTerm)> {
    //     let mut arg_types = vec![];
    //     for (arg_name, arg_type_exp) in expressions {
    //         let arg_type = Cic::elaborate_expression(arg_type_exp);
    //         arg_types.push((arg_name, arg_type));
    //     }

    //     arg_types
    // }

    // fn build_inductive_target(
    //     params: &[(String, CicTerm)],
    //     base: CicTerm,
    // ) -> CicTerm {
    //     if params.is_empty() {
    //         return base;
    //     }

    //     let ((param_name, _param_type), rest) = params.split_first().unwrap();
    //     build_inductive_target(
    //         rest,
    //         CicTerm::Application(
    //             Box::new(base),
    //             Box::new(CicTerm::Variable(param_name.to_string())),
    //         ),
    //     )
    // }

    // let params_types = map_args_to_terms(parameters);
    // let ariety_term = Cic::elaborate_expression(ariety);
    // let _ = Cic::type_check(ariety_term.clone(), environment);
    // let ind_base = build_inductive_target(
    //     &params_types,
    //     CicTerm::Variable(type_name.clone()),
    // );
    // let _ = Cic::type_check(ind_base.clone(), environment);

    // for (constr_name, args) in constructors {
    //     let arg_types = map_args_to_terms(args);
    //     let constr_base_type =
    //         make_multiarg_fun_type(&arg_types, ind_base.clone());
    //     let constr_full_type =
    //         make_multiarg_fun_type(&params_types, constr_base_type);

    //     //TODO add check of the ariety of the constructor
    //     environment.add_variable_to_context(&constr_name, &constr_full_type);
    // }

    // //TODO check positivity
    // environment.add_variable_to_context(
    //     &type_name,
    //     &make_multiarg_fun_type(&params_types, ariety_term),
    // );
    // Ok(())
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
) -> Result<(), String> {
    let assigned_term = Cic::elaborate_expression(body);
    //this type is implicitly typed checked by the equality on assigned_type
    let var_type_term = Cic::elaborate_expression(var_type);
    let assigned_type = Cic::type_check(assigned_term.clone(), environment)?;

    if assigned_type == var_type_term {
        environment.add_variable_definition(
            &var_name,
            &assigned_term,
            &assigned_type,
        );
        Ok(())
    } else {
        Err(
        format!(
            "Missmatch in variable and body types: specified body type is {:?} but body has type {:?}",
            var_type_term, assigned_type
        ))
    }
}

pub fn elaborate_file_root(
    environment: &mut Environment<CicTerm, CicTerm>,
    file_path: String,
    asts: Vec<NsAst>,
) -> Result<(), String> {
    let mut errors = vec![];

    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(stm) => {
                match Cic::elaborate_statement(stm, environment) {
                    Err(message) => errors.push(message),
                    Ok(_) => {}
                }
            }
            NsAst::Exp(exp) => {
                let _ = Cic::elaborate_expression(exp);
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "Elaborating the file {} raised errors:\n{}",
            file_path,
            errors.join("\n")
        ))
    }
}

pub fn elaborate_axiom(
    environment: &mut Environment<CicTerm, CicTerm>,
    axiom_name: String,
    ast: Expression,
) -> Result<(), String> {
    let axiom_forumla = Cic::elaborate_expression(ast);
    // check that _formula_type == PROP?
    let _formula_type = Cic::type_check(axiom_forumla.clone(), environment)?;
    environment.add_variable_to_context(&axiom_name, &axiom_forumla);

    Ok(())
}
//########################### STATEMENTS ELABORATION

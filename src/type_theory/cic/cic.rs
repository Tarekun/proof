use super::evaluation::{
    evaluate_abstraction, evaluate_application, evaluate_axiom,
    evaluate_file_root, evaluate_inductive, evaluate_let, evaluate_match,
    evaluate_type_product, evaluate_var,
};
use crate::parsing::{Expression, NsAst, Statement};
use crate::type_theory::environment::{self, Environment};
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, PartialEq, Clone)] //support toString printing and equality check
pub enum SystemFTerm {
    MissingType(),
    /// (constant's token, constant's type)
    Constant(String, Box<SystemFTerm>),
    /// (sort name)
    Sort(String),
    /// (var name)
    Variable(String),
    /// (var name, var type, body)
    Abstraction(String, Box<SystemFTerm>, Box<SystemFTerm>), //add bodytype?
    /// (var name, var type, body)
    Product(String, Box<SystemFTerm>, Box<SystemFTerm>), //add bodytype?
    /// (function, argument)
    Application(Box<SystemFTerm>, Box<SystemFTerm>),
    /// (matched_term, [ branch: ([pattern], body) ])
    Match(Box<SystemFTerm>, Vec<(Vec<SystemFTerm>, SystemFTerm)>),
}

pub fn type_check(
    term: SystemFTerm,
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
) -> Result<SystemFTerm, String> {
    match term {
        SystemFTerm::Sort(sort_name) => {
            match environment.get_variable_type(&sort_name) {
                Some(sort_type) => Ok(sort_type),
                None => Err(format!("Unbound sort: {}", sort_name)),
            }
        }
        SystemFTerm::Variable(var_name) => {
            match environment.get_variable_type(&var_name) {
                Some(var_type) => Ok(var_type),
                None => Err(format!("Unbound variable: {}", var_name)),
            }
        }
        SystemFTerm::Abstraction(var_name, var_type, body) => {
            let _ = type_check(*var_type.clone(), environment)?;
            //TODO update the context only temporarily, during body evaluation
            environment.add_variable_to_context(&var_name, &var_type);
            let body_type = type_check(*body, environment)?;

            Ok(SystemFTerm::Product(
                var_name,
                var_type,
                Box::new(body_type),
            ))
        }
        SystemFTerm::Product(var_name, var_type, body) => {
            let _ = type_check(*var_type.clone(), environment)?;
            //TODO update the context only temporarily, during body evaluation
            environment.add_variable_to_context(&var_name, &var_type);
            let body_type = type_check(*body, environment)?;

            match body_type {
                SystemFTerm::Sort(_) => Ok(body_type),
                _ => Err(format!("Body of product term must be of type sort, i.e. must be a type, not {:?}", body_type)),
            }
        }
        SystemFTerm::Application(left, right) => {
            let function_type = type_check(*left, environment)?;
            let arg_type = type_check(*right, environment)?;

            match function_type {
                SystemFTerm::Product(_, domain, codomain) => {
                    if *domain == arg_type {
                        Ok(*codomain)
                    } else {
                        Err(format!(
                            "Function and argument have uncompatible types: function expects a {:?} but the argument has type {:?}", 
                            *domain,
                            arg_type
                        ))
                    }
                }
                _ => Err(format!("Attempted application on non functional term of type: {:?}", function_type)),
            }
        }
        SystemFTerm::Match(matched_term, branches) => {
            let matching_type = type_check(*matched_term, environment)?;
            let mut return_type = None;

            fn type_check_pattern(
                constr_type: SystemFTerm,
                variables: Vec<SystemFTerm>,
                environment: &mut Environment<SystemFTerm, SystemFTerm>,
            ) -> Result<SystemFTerm, String> {
                match variables.len() {
                    0 => Ok(constr_type),
                    1.. => match variables[0].clone() {
                        SystemFTerm::Variable(var_name) => match constr_type {
                            SystemFTerm::Product(_, domain, codomain) => {
                                // TODO local addition for the branch only
                                environment.add_variable_to_context(
                                    &var_name, &domain,
                                );
                                type_check_pattern(
                                    *codomain,
                                    variables[1..].to_vec(),
                                    environment,
                                )
                            }
                            _ => Err("Mismatch in number of variables for constructor".to_string()),
                        },
                        _ => Err(format!(
                            "Found illegal term in place of variable {:?}",
                            variables[0].clone(),
                        )),
                    },
                }
            }

            for (pattern, body) in branches {
                let constr_var = pattern[0].clone();
                //type check pattern (i.e. constr exists)
                let constr_type = type_check(constr_var, environment)?;
                let result_type = type_check_pattern(
                    constr_type,
                    pattern[1..].to_vec(),
                    environment,
                )?;
                //make sure pattern makes a type of matching_type
                if result_type != matching_type {
                    return Err(
                        format!(
                            "Pattern doesnt produce expected type: expected {:?} produced {:?}",
                            matching_type,
                            result_type
                        )
                    );
                }

                // match constr_var {
                //     SystemFTerm::Variable(constr_name) => {
                //         //type check pattern (i.e. constr exists)
                //         match environment.get_from_context(&constr_name) {
                //             Some((_, constr_type)) => {
                //                 let result_type = type_check_pattern(constr_type.clone(), pattern[1..].to_vec(), environment)?;
                //                 //make sure pattern makes a type of matching_type
                //                 if result_type != matching_type {
                //                     return Err(
                //                         format!(
                //                             "Pattern doesnt produce expected type: expected {:?} produced {:?}",
                //                             matching_type,
                //                             result_type
                //                         )
                //                     );
                //                 }

                //             },
                //             None => return Err(
                //                 format!(
                //                     "Found unbound type constructor {:?}",
                //                     constr_name,
                //                 )
                //             ),
                //         }
                //     }
                //     _ => return Err(
                //         format!(
                //             "Found illegal term {:?} in place of branch pattern constructor",
                //             constr_var,
                //         )
                //     ),
                // }

                let body_type = type_check(body, environment)?;
                if return_type.is_none() {
                    return_type = Some(body_type);
                } else if return_type.clone().unwrap() != body_type {
                    return Err(
                        format!(
                            "Match branches have different types: found {:?} with previous {:?}",
                            body_type,
                            return_type.unwrap()
                        )
                    );
                }
            }

            Ok(return_type.unwrap())
        }

        _ => Err("Term case is not typable yet".to_string()),
    }
}

pub struct Cic;
impl TypeTheory for Cic {
    type Term = SystemFTerm;
    type Type = SystemFTerm;

    fn evaluate_expression(
        ast: Expression,
        environment: &mut Environment<SystemFTerm, SystemFTerm>,
    ) -> (SystemFTerm, SystemFTerm) {
        match ast {
            Expression::VarUse(var_name) => {
                evaluate_var(&environment, &var_name)
            }
            Expression::Abstraction(var_name, var_type, body) => {
                evaluate_abstraction(environment, var_name, *var_type, *body)
            }
            Expression::TypeProduct(var_name, var_type, body) => {
                evaluate_type_product(environment, var_name, *var_type, *body)
            }
            Expression::Application(left, right) => {
                evaluate_application(environment, *left, *right)
            }
            Expression::Let(var_name, body) => {
                evaluate_let(environment, var_name, *body)
            }
            Expression::Match(matched_term, branches) => {
                evaluate_match(environment, *matched_term, branches)
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_statement(
        ast: Statement,
        environment: &mut Environment<SystemFTerm, SystemFTerm>,
    ) {
        match ast {
            Statement::Comment() => {}
            Statement::FileRoot(file_path, asts) => {
                evaluate_file_root(environment, file_path, asts);
            }
            Statement::Axiom(axiom_name, ast) => {
                evaluate_axiom(environment, axiom_name, *ast);
            }
            Statement::Inductive(type_name, constructors) => {
                evaluate_inductive(environment, type_name, constructors);
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_ast(ast: NsAst) -> Environment<SystemFTerm, SystemFTerm> {
        let mut env = make_default_environment();
        match ast {
            NsAst::Stm(stm) => Cic::evaluate_statement(stm, &mut env),
            NsAst::Exp(exp) => {
                let (_, _) = Cic::evaluate_expression(exp, &mut env);
            }
        }

        env
    }
}

#[allow(non_snake_case)]
pub fn make_default_environment() -> Environment<SystemFTerm, SystemFTerm> {
    let TYPE = SystemFTerm::Sort("TYPE".to_string());
    let axioms: Vec<(&str, &SystemFTerm)> =
        vec![("TYPE", &TYPE), ("PROP", &TYPE)];

    Environment::with_defaults(axioms, Vec::default())
}

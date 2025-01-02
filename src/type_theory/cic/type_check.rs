use super::cic::{Cic, CicTerm};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

pub fn type_check_sort(
    environment: &mut Environment<CicTerm, CicTerm>,
    sort_name: String,
) -> Result<CicTerm, String> {
    match environment.get_variable_type(&sort_name) {
        //TODO check that the type is a sort itself?
        Some(sort_type) => Ok(sort_type),
        None => Err(format!("Unbound sort: {}", sort_name)),
    }
}

pub fn type_check_variable(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
) -> Result<CicTerm, String> {
    match environment.get_variable_type(&var_name) {
        Some(var_type) => Ok(var_type),
        None => Err(format!("Unbound variable: {}", var_name)),
    }
}

pub fn type_check_abstraction(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
    var_type: CicTerm,
    body: CicTerm,
) -> Result<CicTerm, String> {
    let _ = Cic::type_check(var_type.clone(), environment)?;
    //TODO update the context only temporarily, during body evaluation
    environment.add_variable_to_context(&var_name, &var_type);
    let body_type = Cic::type_check(body, environment)?;

    Ok(CicTerm::Product(
        var_name,
        Box::new(var_type),
        Box::new(body_type),
    ))
}

pub fn type_check_product(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
    var_type: CicTerm,
    body: CicTerm,
) -> Result<CicTerm, String> {
    let _ = Cic::type_check(var_type.clone(), environment)?;
    //TODO update the context only temporarily, during body evaluation
    environment.add_variable_to_context(&var_name, &var_type);
    let body_type = Cic::type_check(body, environment)?;

    match body_type {
        CicTerm::Sort(_) => Ok(body_type),
        _ => Err(format!("Body of product term must be of type sort, i.e. must be a type, not {:?}", body_type)),
    }
}

pub fn type_check_application(
    environment: &mut Environment<CicTerm, CicTerm>,
    left: CicTerm,
    right: CicTerm,
) -> Result<CicTerm, String> {
    let function_type = Cic::type_check(left, environment)?;
    let arg_type = Cic::type_check(right, environment)?;

    match function_type {
        CicTerm::Product(_, domain, codomain) => {
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
        _ => Err(format!(
            "Attempted application on non functional term of type: {:?}",
            function_type
        )),
    }
}

fn type_check_pattern(
    constr_type: CicTerm,
    variables: Vec<CicTerm>,
    environment: &mut Environment<CicTerm, CicTerm>,
) -> Result<CicTerm, String> {
    match variables.len() {
        0 => Ok(constr_type),
        1.. => match variables[0].clone() {
            CicTerm::Variable(var_name) => match constr_type {
                CicTerm::Product(_, domain, codomain) => {
                    // TODO local addition for the branch only
                    environment.add_variable_to_context(&var_name, &domain);
                    type_check_pattern(
                        *codomain,
                        variables[1..].to_vec(),
                        environment,
                    )
                }
                _ => Err("Mismatch in number of variables for constructor"
                    .to_string()),
            },
            _ => Err(format!(
                "Found illegal term in place of variable {:?}",
                variables[0].clone(),
            )),
        },
    }
}

pub fn type_check_match(
    environment: &mut Environment<CicTerm, CicTerm>,
    matched_term: CicTerm,
    branches: Vec<(Vec<CicTerm>, CicTerm)>,
) -> Result<CicTerm, String> {
    let matching_type = Cic::type_check(matched_term, environment)?;
    let mut return_type = None;

    for (pattern, body) in branches {
        //pattern type checking
        let constr_var = pattern[0].clone();
        let constr_type = Cic::type_check(constr_var, environment)?;
        let result_type = type_check_pattern(
            constr_type,
            pattern[1..].to_vec(),
            environment,
        )?;
        if result_type != matching_type {
            return Err(
                format!(
                    "Pattern doesnt produce expected type: expected {:?} produced {:?}",
                    matching_type,
                    result_type
                )
            );
        }

        //body type checking
        let body_type = Cic::type_check(body, environment)?;
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

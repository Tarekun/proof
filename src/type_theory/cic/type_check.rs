use super::cic::{Cic, SystemFTerm};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

pub fn type_check_sort(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    sort_name: String,
) -> Result<SystemFTerm, String> {
    match environment.get_variable_type(&sort_name) {
        //TODO check that the type is a sort itself?
        Some(sort_type) => Ok(sort_type),
        None => Err(format!("Unbound sort: {}", sort_name)),
    }
}

pub fn type_check_variable(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    var_name: String,
) -> Result<SystemFTerm, String> {
    match environment.get_variable_type(&var_name) {
        Some(var_type) => Ok(var_type),
        None => Err(format!("Unbound variable: {}", var_name)),
    }
}

pub fn type_check_abstraction(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    var_name: String,
    var_type: SystemFTerm,
    body: SystemFTerm,
) -> Result<SystemFTerm, String> {
    let _ = Cic::type_check(var_type.clone(), environment)?;
    //TODO update the context only temporarily, during body evaluation
    environment.add_variable_to_context(&var_name, &var_type);
    let body_type = Cic::type_check(body, environment)?;

    Ok(SystemFTerm::Product(
        var_name,
        Box::new(var_type),
        Box::new(body_type),
    ))
}

pub fn type_check_product(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    var_name: String,
    var_type: SystemFTerm,
    body: SystemFTerm,
) -> Result<SystemFTerm, String> {
    let _ = Cic::type_check(var_type.clone(), environment)?;
    //TODO update the context only temporarily, during body evaluation
    environment.add_variable_to_context(&var_name, &var_type);
    let body_type = Cic::type_check(body, environment)?;

    match body_type {
        SystemFTerm::Sort(_) => Ok(body_type),
        _ => Err(format!("Body of product term must be of type sort, i.e. must be a type, not {:?}", body_type)),
    }
}

pub fn type_check_application(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    left: SystemFTerm,
    right: SystemFTerm,
) -> Result<SystemFTerm, String> {
    let function_type = Cic::type_check(left, environment)?;
    let arg_type = Cic::type_check(right, environment)?;

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
        _ => Err(format!(
            "Attempted application on non functional term of type: {:?}",
            function_type
        )),
    }
}

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
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    matched_term: SystemFTerm,
    branches: Vec<(Vec<SystemFTerm>, SystemFTerm)>,
) -> Result<SystemFTerm, String> {
    let matching_type = Cic::type_check(matched_term, environment)?;
    let mut return_type = None;

    for (pattern, body) in branches {
        let constr_var = pattern[0].clone();
        //type check pattern (i.e. constr exists)
        let constr_type = Cic::type_check(constr_var, environment)?;
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

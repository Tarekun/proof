use crate::type_theory::environment::Environment;

use super::cic::CicTerm;
use super::cic::CicTerm::{Abstraction, Application, Product, Sort, Variable};
use std::fmt;

pub fn delta_reduce(
    environment: &Environment<CicTerm, CicTerm>,
    term: CicTerm,
) -> Result<CicTerm, String> {
    match term {
        Variable(var_name) => {
            if let Some((_, (body, _))) = environment.get_from_deltas(&var_name)
            {
                Ok(body.to_owned())
            } else {
                Err(format!("Variable {} is not present in Δ so it doesnt have a substitution", var_name))
            }
        }
        _ => Err(format!(
            "Term {:?} is not δ-reducable because it's not a variable",
            term
        )),
    }
}

fn term_formatter(term: &CicTerm, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match term {
        // (sort name)
        CicTerm::Sort(name) => write!(f, "{}", name),
        // (var name)
        CicTerm::Variable(name) => write!(f, "{}", name),
        CicTerm::Abstraction(var_name, var_type, body) => {
            write!(f, "λ{}:{}. {}", var_name, var_type, body)
        }
        CicTerm::Product(var_name, domain, codomain) => {
            write!(f, "Π{}:{}. {}", var_name, domain, codomain)
        }
        CicTerm::Application(func, arg) => write!(f, "({} {})", func, arg),
        // (matched_term, [ branch: ([pattern], body) ])
        CicTerm::Match(matched_term, branches) => {
            write!(f, "match {} {{ ", matched_term)?;
            for (patterns, body) in branches {
                write!(f, "[")?;
                for (i, pattern) in patterns.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", pattern)?;
                }
                write!(f, "] => {}; ", body)?;
            }
            write!(f, "}}")
        }
    }
}
impl fmt::Display for CicTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        term_formatter(self, f)
    }
}
impl fmt::Debug for CicTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        term_formatter(self, f)
    }
}
/// Given the CIC type of a function `fun` returns the number of arguments of the function
// pub fn args_len(fun: &CicTerm) -> i32 {
//     match fun {
//         Product(_, _, codomain) => 1 + args_len(codomain),
//         _ => 0,
//     }
// }

/// Returns variable terms from a multi argument function
pub fn get_variables_as_terms(fun_type: &CicTerm) -> Vec<CicTerm> {
    match fun_type {
        Product(var_name, _domain, codomain) => {
            let mut rec: Vec<CicTerm> = get_variables_as_terms(codomain);
            let mut result = vec![Variable(var_name.to_owned())];
            result.append(&mut rec);
            result
        }
        _ => {
            vec![] //discard the base type
        }
    }
}

/// Returns the list of types of the arguments of a multi arg function
pub fn get_arg_types(fun_type: &CicTerm) -> Vec<CicTerm> {
    match fun_type {
        Product(_, domain, codomain) => {
            let mut result: Vec<CicTerm> = vec![(**domain).clone()];
            result.extend(get_arg_types(&codomain));
            return result;
        }
        _ => vec![],
    }
}

/// Takes a function term and returns an application term of all the arguments given
pub fn apply_arguments(fun: &CicTerm, args: Vec<CicTerm>) -> CicTerm {
    let mut application = fun.clone();
    for arg in args {
        application = Application(Box::new(application), Box::new(arg));
    }

    application
}

/// Clones the given product, swapping the innermost body term with the given one
pub fn clone_product_with_different_result(
    product: &CicTerm,
    new_result: CicTerm,
) -> CicTerm {
    match product {
        Product(var_name, domain, codomain) => {
            let new_codomain =
                clone_product_with_different_result(codomain, new_result);
            Product(var_name.to_owned(), domain.clone(), Box::new(new_codomain))
        }
        Sort(_) => new_result,
        Variable(_) => new_result,
        _ => panic!("TODO: handle better"),
    }
}

/// Returns the innermost body term of a serie of concatenated Products
/// (ie the return type of a function)
pub fn get_prod_innermost(term: &CicTerm) -> &CicTerm {
    match term {
        Product(_, _, codomain) => get_prod_innermost(&*codomain),
        _ => term,
    }
}

/// Given a multiarg application term, returns the vector of all the arguments being applyed
pub fn application_args(application: CicTerm) -> Vec<CicTerm> {
    match application {
        Application(left, right) => {
            let mut rec = application_args(*left);
            rec.push(*right); //TODO shouldnt it be append/enqueue?
            return rec;
        }
        // discard leftmost term, we dont care about the function
        _ => vec![],
    }
}

/// Given a multiarg application term, returns the outermost term element (ie the function
/// being applied)
pub fn get_applied_function(application: &CicTerm) -> CicTerm {
    match application {
        Application(left, _) => get_applied_function(left),
        _ => application.to_owned(),
    }
}

/// Returns `true` if `term` is an instance of type with name `name`, `false` otherwise
pub fn is_instance_of(term: &CicTerm, name: &str) -> bool {
    match term {
        Variable(var_name) => var_name == name,
        Application(dep_type, _args) => is_instance_of(&dep_type, name),
        // anything else isnt a referencable type
        _ => false,
    }
}

pub fn references(term: &CicTerm, name: &str) -> bool {
    match term {
        Variable(var_name) => var_name == name,
        Sort(sort_name) => sort_name == name,
        Application(left, rigth) => {
            references(&left, name) || references(&rigth, name)
        }
        Abstraction(_, domain, codomain) => {
            references(&domain, name) || references(&codomain, name)
        }
        Product(_, domain, codomain) => {
            references(&domain, name) || references(&codomain, name)
        }
        // TODO fuck match fr
        _ => false,
    }
}

/// Returns `true` if `name` occurs only positively in `rec_type`, `false` otherwise
pub fn check_positivity(function_type: &CicTerm, name: &str) -> bool {
    let arg_types = get_arg_types(function_type);
    for arg_type in arg_types {
        if references(&arg_type, name) {
            return false;
        }
    }

    true
}

/// Creates the CIC type of a function with named arguments `arg_types`
/// that returns a value of type `base`
pub fn make_multiarg_fun_type(
    arg_types: &[(String, CicTerm)],
    base: &CicTerm,
) -> CicTerm {
    if arg_types.is_empty() {
        return base.clone();
    }

    let ((arg_name, arg_type), rest) = arg_types.split_first().unwrap();
    let sub_type = make_multiarg_fun_type(rest, base);

    CicTerm::Product(
        arg_name.to_string(),
        Box::new(arg_type.to_owned()),
        Box::new(sub_type),
    )
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {}

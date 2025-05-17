use crate::misc::{simple_map, simple_map_indexed};
use crate::type_theory::cic::cic::{
    FIRST_INDEX, GLOBAL_INDEX, PLACEHOLDER_DBI,
};
use crate::type_theory::commons::utils::generic_multiarg_fun_type;
use crate::type_theory::environment::Environment;

use super::cic::CicTerm::{
    Abstraction, Application, Match, Meta, Product, Sort, Variable,
};
use super::cic::{Cic, CicTerm};
use std::collections::HashMap;
use std::fmt;

pub fn delta_reduce(
    environment: &Environment<CicTerm, CicTerm>,
    term: CicTerm,
) -> Result<CicTerm, String> {
    match term {
        Variable(var_name, _) => {
            if let Some((_, body)) = environment.get_from_deltas(&var_name) {
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
        Sort(name) => write!(f, "{}", name),
        // (var name)
        Variable(name, dbi) => {
            let dbi_text = if *dbi == GLOBAL_INDEX {
                "G"
            } else if *dbi == PLACEHOLDER_DBI {
                "P"
            } else {
                &dbi.to_string()
            };
            write!(f, "{}|{}", name, dbi_text)
        }
        Abstraction(var_name, var_type, body) => {
            write!(f, "λ{}:{}. {}", var_name, var_type, body)
        }
        Product(var_name, domain, codomain) => {
            write!(f, "Π{}:{}. {}", var_name, domain, codomain)
        }
        Application(func, arg) => write!(f, "({} {})", func, arg),
        // (matched_term, [ branch: ([pattern], body) ])
        Match(matched_term, branches) => {
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
        Meta(index) => write!(f, "?[{}]", index),
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
    fn solver(fun_type: &CicTerm, index: i32) -> Vec<CicTerm> {
        match fun_type {
            Product(var_name, _domain, codomain) => {
                let mut rec: Vec<CicTerm> = solver(codomain, index + 1);
                let mut result = vec![Variable(var_name.to_owned(), index)];
                result.append(&mut rec);
                result
            }
            _ => {
                vec![] //discard the base type
            }
        }
    }

    solver(fun_type, 0)
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
        Variable(_, _) => new_result,
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
        Variable(var_name, _) => var_name == name,
        Application(dep_type, _args) => is_instance_of(&dep_type, name),
        // anything else isnt a referencable type
        _ => false,
    }
}

/// Given a `term` returns `true` if it contains a reference to the variable `name`
pub fn references(term: &CicTerm, name: &str) -> bool {
    match term {
        Variable(var_name, _) => var_name == name,
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

/// Returns `term` where each instance of the meta variable `target` is swapped with `arg`
pub fn substitute_meta(term: &CicTerm, target: &i32, arg: &CicTerm) -> CicTerm {
    match term {
        Meta(index) => {
            if index == target {
                arg.clone()
            } else {
                term.clone()
            }
        }
        Sort(_) => term.clone(),
        Variable(_, _) => term.clone(),
        Application(left, right) => Application(
            Box::new(substitute_meta(left, target, arg)),
            Box::new(substitute_meta(right, target, arg)),
        ),
        // TODO: dont carry substitution if names match to implement overriding of names
        Abstraction(var_name, domain, codomain) => Abstraction(
            var_name.to_string(),
            Box::new(substitute_meta(domain, target, arg)),
            Box::new(substitute_meta(codomain, target, arg)),
        ),
        Product(var_name, domain, codomain) => Product(
            var_name.to_string(),
            Box::new(substitute_meta(domain, target, arg)),
            Box::new(substitute_meta(codomain, target, arg)),
        ),
        Match(matched_term, branches) => Match(
            Box::new(substitute_meta(matched_term, target, arg)),
            //TODO i dont want to clone branches here tbh
            simple_map(branches.clone(), |(pattern, body)| {
                (
                    simple_map(pattern, |term| {
                        substitute_meta(&term, target, arg)
                    }),
                    substitute_meta(&body, target, arg),
                )
            }),
        ),
    }
}

/// Given a `term` and a variable, returns a term where each instance of
/// `var_name` is substituted with `arg`
pub fn substitute(term: &CicTerm, target_name: &str, arg: &CicTerm) -> CicTerm {
    match term {
        Sort(_) => term.clone(),
        Variable(var_name, _) => {
            if var_name == target_name {
                arg.clone()
            } else {
                term.clone()
            }
        }
        Application(left, right) => Application(
            Box::new(substitute(left, target_name, arg)),
            Box::new(substitute(right, target_name, arg)),
        ),
        // TODO: dont carry substitution if names match to implement overriding of names
        Abstraction(var_name, domain, codomain) => Abstraction(
            var_name.to_string(),
            Box::new(substitute(domain, target_name, arg)),
            Box::new(substitute(codomain, target_name, arg)),
        ),
        Product(var_name, domain, codomain) => Product(
            var_name.to_string(),
            Box::new(substitute(domain, target_name, arg)),
            Box::new(substitute(codomain, target_name, arg)),
        ),
        Match(matched_term, branches) => Match(
            Box::new(substitute(matched_term, target_name, arg)),
            //TODO i dont want to clone branches here tbh
            simple_map(branches.clone(), |(pattern, body)| {
                (
                    simple_map(pattern, |term| {
                        substitute(&term, target_name, arg)
                    }),
                    substitute(&body, target_name, arg),
                )
            }),
        ),
        //TODO implementare qua la sostituzione delle metavariabili?
        Meta(_) => term.clone(),
    }
}

/// Creates the CIC type of a function with named arguments `arg_types`
/// that returns a value of type `base`
pub fn make_multiarg_fun_type(
    arg_types: &[(String, CicTerm)],
    base: &CicTerm,
) -> CicTerm {
    generic_multiarg_fun_type::<Cic, _>(
        arg_types,
        base,
        |arg_name, arg_type, sub_type| {
            CicTerm::Product(arg_name, Box::new(arg_type), Box::new(sub_type))
        },
    )
}

pub fn eta_expand(args: &[(String, CicTerm)], body: &CicTerm) -> CicTerm {
    fn solver(mut args: Vec<(String, CicTerm)>, body: CicTerm) -> CicTerm {
        if args.is_empty() {
            return body;
        }

        let (arg_name, arg_type) = args.pop().unwrap();
        solver(
            args,
            Abstraction(arg_name, Box::new(arg_type), Box::new(body)),
        )
    }

    solver(args.to_vec(), body.clone())
}

/// Given a term, it enumerates variables with De Bruijn indexes properly
pub fn index_variables(term: &CicTerm) -> CicTerm {
    fn solver(
        term: &CicTerm,
        current_dbi: i32,
        bound_vars: &mut HashMap<String, i32>,
    ) -> CicTerm {
        match term {
            Sort(_) => term.to_owned(),
            Meta(_) => term.to_owned(),
            Variable(name, _) => match bound_vars.get(name) {
                Some(dbi) => Variable(name.to_string(), *dbi),
                // unbound variables in the term get the global variable index
                None => Variable(name.to_string(), GLOBAL_INDEX),
            },
            Abstraction(var_name, var_type, body) => {
                bound_vars.insert(var_name.to_string(), current_dbi);

                Abstraction(
                    var_name.to_string(),
                    Box::new(solver(var_type, current_dbi + 1, bound_vars)),
                    Box::new(solver(body, current_dbi + 1, bound_vars)),
                )
            }
            Product(var_name, var_type, body) => {
                bound_vars.insert(var_name.to_string(), current_dbi);

                Product(
                    var_name.to_string(),
                    Box::new(solver(var_type, current_dbi + 1, bound_vars)),
                    Box::new(solver(body, current_dbi + 1, bound_vars)),
                )
            }
            Application(left, right) => Application(
                Box::new(solver(left, current_dbi, bound_vars)),
                Box::new(solver(right, current_dbi, bound_vars)),
            ),
            Match(matched_term, branches) => {
                let matched_term =
                    solver(matched_term, current_dbi, bound_vars);

                let branches = simple_map(
                    branches.clone(),
                    |(pattern, body): (Vec<CicTerm>, CicTerm)| {
                        let constructor: CicTerm =
                            solver(&pattern[0], current_dbi, bound_vars);
                        let arguments: Vec<CicTerm> = simple_map_indexed(
                            pattern[1..].to_vec(),
                            |(index, arg)| {
                                solver(
                                    &arg,
                                    current_dbi + index as i32,
                                    bound_vars,
                                )
                            },
                        );

                        let args_len = arguments.len() as i32;
                        let mut new_pattern: Vec<CicTerm> = vec![constructor];
                        new_pattern.extend(arguments);

                        (
                            new_pattern,
                            solver(&body, current_dbi + args_len, bound_vars),
                        )
                    },
                );

                Match(Box::new(matched_term), branches)
            }
        }
    }

    solver(term, FIRST_INDEX, &mut HashMap::new())
}
//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::cic::{
        cic::{
            CicTerm::{
                Abstraction, Application, Match, Product, Sort, Variable,
            },
            GLOBAL_INDEX, PLACEHOLDER_DBI,
        },
        cic_utils::index_variables,
    };

    #[test]
    fn test_index_variables() {
        assert_eq!(
            index_variables(&Variable("x".to_string(), PLACEHOLDER_DBI)),
            Variable("x".to_string(), GLOBAL_INDEX),
            "Variable indexer doesnt use the global index properly"
        );

        assert_eq!(
            index_variables(&Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable("y".to_string(), PLACEHOLDER_DBI)),
            )),
            Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable("y".to_string(), 0)),
            ),
            "Abstraction indexing not working"
        );

        assert_eq!(
            index_variables(&Abstraction(
                "a".to_string(),
                Box::new(Variable("Unit".to_string(), PLACEHOLDER_DBI)),
                Box::new(Abstraction(
                    "b".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("b".to_string(), PLACEHOLDER_DBI)),
                )),
            )),
            Abstraction(
                "a".to_string(),
                Box::new(Variable("Unit".to_string(), GLOBAL_INDEX)),
                Box::new(Abstraction(
                    "b".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("b".to_string(), 1)),
                )),
            )
        );

        // // Test 4: Application with variables
        // let app = Application(
        //     Box::new(Abstraction(
        //         "f".to_string(),
        //         Box::new(Sort("TYPE".to_string())),
        //         Box::new(Variable("x".to_string(), 0)),
        //     )),
        //     Box::new(Variable("y".to_string(), 0)),
        // );
        // let expected_app = Application(
        //     Box::new(Abstraction(
        //         "f".to_string(),
        //         Box::new(Sort("TYPE".to_string())),
        //         Box::new(Variable("x".to_string(), 1)),
        //     )),
        //     Box::new(Variable("y".to_string(), 0)),
        // );
        // assert_eq!(index_variables(&app), expected_app);

        // // Test 5: Product with variables
        // let prod = Product(
        //     "f".to_string(),
        //     Box::new(Sort("TYPE".to_string())),
        //     Box::new(Abstraction(
        //         "x".to_string(),
        //         Box::new(Sort("TYPE".to_string())),
        //         Box::new(Variable("y".to_string(), 0)),
        //     )),
        // );
        // let expected_prod = Product(
        //     "f".to_string(),
        //     Box::new(Sort("TYPE".to_string())),
        //     Box::new(Abstraction(
        //         "x".to_string(),
        //         Box::new(Sort("TYPE".to_string())),
        //         Box::new(Variable("y".to_string(), 2)),
        //     )),
        // );
        // assert_eq!(index_variables(&prod), expected_prod);

        // Test 6: Match with variables
        // let match_term = Match(
        //     Box::new(Variable("x".to_string(), 0)),
        //     vec![
        //         vec![Variable("y".to_string(), 0)],
        //         vec![Variable("z".to_string(), 0)],
        //     ],
        // );
        // let expected_match = Match(
        //     Box::new(Variable("x".to_string(), 0)),
        //     vec![
        //         vec![Variable("y".to_string(), 1)],
        //         vec![Variable("z".to_string(), 2)],
        //     ],
        // );
        // assert_eq!(index_variables(&match_term), expected_match);
    }

    // #[test]
    // fn test_delta_reduce() {
    //     // Test delta reduction for variables
    //     let env = Environment::default_environment();
    //     let var = Variable("x".to_string(), 0);
    //     match delta_reduce(&env, var) {
    //         Err(e) => assert_eq!(e, "Variable x is not present in Δ so it doesnt have a substitution"),
    //         Ok(_) => panic!("Expected error for undefined variable"),
    //     }

    //     // Add a substitution and test again
    //     env.add_substitution("x", &Variable("y".to_string(), 0));
    //     match delta_reduce(&env, var) {
    //         Err(e) => panic!("Expected success but got error: {}", e),
    //         Ok(reduced) => assert_eq!(reduced, Variable("y".to_string(), 0)),
    //     }
    // }

    // #[test]
    // fn test_term_formatter() {
    //     // Test formatting for different term types
    //     let sort = Sort("TYPE".to_string());
    //     let var = Variable("x".to_string(), 0);
    //     let abs = Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0)));
    //     let app = Application(Box::new(abs.clone()), Box::new(var.clone()));

    //     assert_eq!(format!("{}", sort), "TYPE");
    //     assert_eq!(format!("{}", var), "x");
    //     assert_eq!(format!("{}", abs), "λf:TYPE. x");
    //     assert_eq!(format!("{}", app), "(λf:TYPE. x x)");
    // }

    // #[test]
    // fn test_get_variables_as_terms() {
    //     // Test getting variables from a function type
    //     let fun_type = make_multiarg_fun_type(
    //         &[("x".to_string(), Sort("TYPE".to_string())), ("y".to_string(), Sort("PROP".to_string()))],
    //         &Sort("TYPE".to_string()),
    //     );
    //     assert_eq!(get_variables_as_terms(&fun_type), vec![Variable("x".to_string(), 0), Variable("y".to_string(), 1)]);
    // }

    // #[test]
    // fn test_get_arg_types() {
    //     // Test getting argument types from a function type
    //     let fun_type = make_multiarg_fun_type(
    //         &[("x".to_string(), Sort("TYPE".to_string())), ("y".to_string(), Sort("PROP".to_string()))],
    //         &Sort("TYPE".to_string()),
    //     );
    //     assert_eq!(get_arg_types(&fun_type), vec![Sort("TYPE".to_string()), Sort("PROP".to_string())]);
    // }

    // #[test]
    // fn test_apply_arguments() {
    //     // Test applying arguments to a function
    //     let fun = Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0)));
    //     let args = vec![Variable("y".to_string(), 0)];
    //     assert_eq!(apply_arguments(&fun, args), Application(Box::new(fun.clone()), Box::new(Variable("y".to_string(), 0))));
    // }

    // #[test]
    // fn test_clone_product_with_different_result() {
    //     // Test cloning a product with different result
    //     let prod = Product(
    //         "f".to_string(),
    //         Box::new(Sort("TYPE".to_string())),
    //         Box::new(Abstraction("x".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("y".to_string(), 0))))
    //     );
    //     let new_result = Variable("z".to_string(), 0);
    //     assert_eq!(
    //         clone_product_with_different_result(&prod, new_result),
    //         Product(
    //             "f".to_string(),
    //             Box::new(Sort("TYPE".to_string())),
    //             Box::new(Abstraction("x".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(new_result.clone())))
    //         )
    //     );
    // }

    // #[test]
    // fn test_get_prod_innermost() {
    //     // Test getting the innermost body of a product
    //     let prod = Product(
    //         "f".to_string(),
    //         Box::new(Sort("TYPE".to_string())),
    //         Box::new(Product("g".to_string(), Box::new(Sort("PROP".to_string())), Box::new(Variable("x".to_string(), 0))))
    //     );
    //     assert_eq!(get_prod_innermost(&prod), &Variable("x".to_string(), 0));
    // }

    // #[test]
    // fn test_application_args() {
    //     // Test getting arguments from an application
    //     let app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     assert_eq!(application_args(app), vec![Variable("y".to_string(), 0)]);
    // }

    // #[test]
    // fn test_get_applied_function() {
    //     // Test getting the applied function from an application
    //     let app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     assert_eq!(get_applied_function(&app), Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0))));
    // }

    // #[test]
    // fn test_is_instance_of() {
    //     // Test checking if a term is an instance of a type
    //     let var = Variable("Nat".to_string(), 0);
    //     assert!(is_instance_of(&var, "Nat"));
    //     assert!(!is_instance_of(&var, "Bool"));
    // }

    // #[test]
    // fn test_references() {
    //     // Test checking if a term references a variable
    //     let app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     assert!(references(&app, "x"));
    //     assert!(!references(&app, "z"));
    // }

    // #[test]
    // fn test_check_positivity() {
    //     // Test checking positivity of a variable in a function type
    //     let fun_type = make_multiarg_fun_type(
    //         &[],
    //         &Sort("TYPE".to_string()),
    //     );
    //     assert!(check_positivity(&fun_type, "x"));
    // }

    // #[test]
    // fn test_substitute_meta() {
    //     // Test substituting a meta variable
    //     let term = Meta(0);
    //     let arg = Variable("x".to_string(), 0);
    //     assert_eq!(substitute_meta(&term, &0, &arg), arg.clone());
    //     assert_ne!(substitute_meta(&term, &1, &arg), arg);
    // }

    // #[test]
    // fn test_substitute() {
    //     // Test substituting a variable
    //     let term = Variable("x".to_string(), 0);
    //     let arg = Variable("y".to_string(), 0);
    //     assert_eq!(substitute(&term, "x", &arg), arg.clone());
    //     assert_ne!(substitute(&term, "z", &arg), arg);
    // }

    // #[test]
    // fn test_make_multiarg_fun_type() {
    //     // Test creating a multi-argument function type
    //     let fun_type = make_multiarg_fun_type(
    //         &[("x".to_string(), Sort("TYPE".to_string())), ("y".to_string(), Sort("PROP".to_string()))],
    //         &Sort("TYPE".to_string()),
    //     );
    //     assert_eq!(fun_type, Product("x", Box::new(Sort("TYPE".to_string())), Box::new(Product("y", Box::new(Sort("PROP".to_string())), Box::new(Sort("TYPE".to_string()))))));
    // }

    // #[test]
    // fn test_eta_expand() {
    //     // Test eta expansion
    //     let body = Variable("x".to_string(), 0);
    //     let args = vec![("y".to_string(), Sort("TYPE".to_string()))];
    //     assert_eq!(
    //         eta_expand(&args, &body),
    //         Abstraction("y", Box::new(Sort("TYPE".to_string())), Box::new(body.clone()))
    //     );
    // }

    // #[test]
    // fn test_index_variables() {
    //     // Test index variables function
    //     let var = Variable("x".to_string(), 0);
    //     assert_eq!(index_variables(&var), var);

    //     let abs = Abstraction("y".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("z".to_string(), 0)));
    //     let expected_abs = Abstraction("y".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("z".to_string(), 1)));
    //     assert_eq!(index_variables(&abs), expected_abs);

    //     let nested_abs = Abstraction(
    //         "a".to_string(),
    //         Box::new(Abstraction("b".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("c".to_string(), 0)))),
    //         Box::new(Variable("d".to_string(), 0))
    //     );
    //     let expected_nested_abs = Abstraction(
    //         "a".to_string(),
    //         Box::new(Abstraction("b".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("c".to_string(), 2)))),
    //         Box::new(Variable("d".to_string(), 1))
    //     );
    //     assert_eq!(index_variables(&nested_abs), expected_nested_abs);

    //     let app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 0)))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     let expected_app = Application(
    //         Box::new(Abstraction("f".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("x".to_string(), 1)))),
    //         Box::new(Variable("y".to_string(), 0))
    //     );
    //     assert_eq!(index_variables(&app), expected_app);

    //     let prod = Product(
    //         "f".to_string(),
    //         Box::new(Sort("TYPE".to_string())),
    //         Box::new(Abstraction("x".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("y".to_string(), 0))))
    //     );
    //     let expected_prod = Product(
    //         "f".to_string(),
    //         Box::new(Sort("TYPE".to_string())),
    //         Box::new(Abstraction("x".to_string(), Box::new(Sort("TYPE".to_string())), Box::new(Variable("y".to_string(), 2))))
    //     );
    //     assert_eq!(index_variables(&prod), expected_prod);

    //     let match_term = Match(
    //         Box::new(Variable("x".to_string(), 0)),
    //         vec![vec![Variable("y".to_string(), 0)], vec![Variable("z".to_string(), 0)]]
    //     );
    //     let expected_match = Match(
    //         Box::new(Variable("x".to_string(), 0)),
    //         vec![vec![Variable("y".to_string(), 1)], vec![Variable("z".to_string(), 2)]]
    //     );
    //     assert_eq!(index_variables(&match_term), expected_match);
    // }
}

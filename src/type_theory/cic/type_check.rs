use super::cic::CicTerm::{Application, Product, Sort, Variable};
use super::cic::{Cic, CicTerm};
use crate::misc::{simple_map, simple_map_indexed};
use crate::type_theory::cic::cic_utils::{application_args, apply_arguments, clone_product_with_different_result, delta_reduce, get_arg_types, get_prod_innermost, get_variables_as_terms, is_instance_of};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;


//########################### EXPRESSIONS TYPE CHECKING
//
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
//
//
pub fn type_check_variable(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
) -> Result<CicTerm, String> {
    match environment.get_variable_type(&var_name) {
        Some(var_type) => Ok(var_type),
        None => Err(format!("Unbound variable: {}", var_name)),
    }
}
//
//
pub fn type_check_abstraction(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
    var_type: CicTerm,
    body: CicTerm,
) -> Result<CicTerm, String> {
    let types_sort = Cic::type_check_term(var_type.clone(), environment)?;
    let _ = check_is_sort(&types_sort)?;

    environment.with_local_declaration(
        &var_name.clone(),
        &var_type.clone(),
        |local_env| {
            let body_type = Cic::type_check_term(body, local_env)?;

            Ok(CicTerm::Product(
                var_name,
                Box::new(var_type),
                Box::new(body_type),
            ))
        },
    )
}
//
//
pub fn type_check_product(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
    var_type: CicTerm,
    body: CicTerm,
) -> Result<CicTerm, String> {
    let types_sort = Cic::type_check_term(var_type.clone(), environment)?;
    let _ = check_is_sort(&types_sort)?;

    environment.with_local_declaration(
        &var_name,
        &var_type,
        |local_env| {
            let body_type = Cic::type_check_term(body, local_env)?;

            match body_type {
                CicTerm::Sort(_) => Ok(body_type),
                _ => Err(format!("Body of product term must be of type sort, i.e. must be a type, not {:?}", body_type)),
            }
        },
    )
}
//
//
pub fn type_check_application(
    environment: &mut Environment<CicTerm, CicTerm>,
    left: CicTerm,
    right: CicTerm,
) -> Result<CicTerm, String> {
    fn type_check_nested_app(
        local_env: &mut Environment<CicTerm, CicTerm>,
        term: CicTerm,
    ) -> Result<CicTerm, String> {
        match term {
            Application(left, right) => {
                let function_type = type_check_nested_app(local_env, *left.clone())?;
                let arg_type = Cic::type_check_term(*right.clone(), local_env)?;
    
                match function_type.clone() {
                    CicTerm::Product(var_name, domain, codomain) => {
                        if Cic::terms_unify(local_env, &(*domain), &arg_type) {
                            local_env.add_variable_definition(&var_name, &right, &arg_type);
                            //se è una variabile già applicata, fai la sostituzione
                            match delta_reduce(local_env, *codomain.clone()) {
                                Ok(body) => Ok(body),
                                _ => Ok(*codomain)
                            }
                        } else {
                            Err(format!(
                                "Function and argument have uncompatible types: function expects a {:?} but the argument has type {:?}", 
                                *domain,
                                arg_type
                            ))
                        }
                    }
                    _ => Err(format!(
                        "Attempted application on non functional term '{:?}' of type: {:?}",
                        left,
                        function_type
                    )),
                }
            },
            _ => {
                let term_type = Cic::type_check_term(term, local_env)?;
                Ok(term_type)
            }
        }
    }

    environment.with_rollback(|local_env| {
        type_check_nested_app(local_env, Application(Box::new(left), Box::new(right)))
    })
}
//
//
fn type_constr_vars(
    constr_type: &CicTerm,
    variables: Vec<CicTerm>,
) -> Vec<(String, CicTerm)> {
    match variables.len() {
        0 => vec![],
        1.. => match &variables[0] {
            CicTerm::Variable(var_name) => match constr_type {
                CicTerm::Product(_, domain, codomain) => {
                    let mut typed_vars =
                        type_constr_vars(&(*codomain), variables[1..].to_vec());
                    typed_vars.insert(0, (var_name.clone(), *(domain.clone())));
                    typed_vars
                }
                // i dont want to return results here
                _ => {
                    panic!("Mismatch in number of variables for constructor");
                }
            },
            _ => {
                panic!(
                    "Found illegal term in place of variable {:?}",
                    variables[0],
                );
            }
        },
    }
}
fn type_check_pattern(
    constr_type: &CicTerm,
    variables: Vec<CicTerm>,
    environment: &mut Environment<CicTerm, CicTerm>,
) -> Result<CicTerm, String> {
    match variables.len() {
        0 => Ok(constr_type.clone()),
        1.. => match variables[0] {
            CicTerm::Variable(_) => match constr_type {
                CicTerm::Product(_, _, codomain) => {
                    // doesnt need to update the context, here var_name is a type variable, not a term
                    type_check_pattern(
                        &(*codomain),
                        variables[1..].to_vec(),
                        environment,
                    )
                }
                _ => Err("Mismatch in number of variables for constructor"
                    .to_string()),
            },
            _ => Err(format!(
                "Found illegal term in place of variable {:?}",
                variables[0],
            )),
        },
    }
}
pub fn type_check_match(
    environment: &mut Environment<CicTerm, CicTerm>,
    matched_term: CicTerm,
    branches: Vec<(Vec<CicTerm>, CicTerm)>,
) -> Result<CicTerm, String> {
    let matching_type = Cic::type_check_term(matched_term, environment)?;
    let mut return_type = None;

    for (pattern, body) in branches {
        //pattern type checking
        let constr_var = pattern[0].clone();
        let constr_type = Cic::type_check_term(constr_var, environment)?;
        let result_type = type_check_pattern(
            &constr_type,
            pattern[1..].to_vec(),
            environment,
        )?;
        if !Cic::terms_unify(environment, &result_type, &matching_type) {
            return Err(
                format!(
                    "Pattern doesnt produce expected type: expected {:?} produced {:?}",
                    matching_type,
                    result_type
                )
            );
        }

        //body type checking
        let pattern_assumptions =
            type_constr_vars(&constr_type, pattern[1..].to_vec());
        let body_type = environment
            .with_local_declarations(&pattern_assumptions, |local_env| {
                Cic::type_check_term(body, local_env)
            })?;
        if return_type.is_none() {
            return_type = Some(body_type);
        } else if !Cic::terms_unify(
            environment,
            &return_type.clone().unwrap(),
            &body_type,
        ) {
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
//
//########################### EXPRESSIONS TYPE CHECKING
//
//
//########################### STATEMENTS TYPE CHECKING
//
pub fn type_check_let(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
    opt_type: Option<CicTerm>,
    body: CicTerm,
) -> Result<CicTerm, String> {
    let body_type = Cic::type_check_term(body.clone(), environment)?;
    let var_type = if opt_type.is_none() {
        body_type.clone()
    } else {
        opt_type.unwrap()
    };
    let _ = type_check_type(&var_type, environment)?;

    if Cic::terms_unify(environment, &body_type, &var_type) {
        environment.add_variable_definition(&var_name, &body, &var_type);
        Ok(CicTerm::Variable("Unit".to_string()))
    } else {
        Err(format!(
            "In {} definition annotated type {:?} and body type {:?} do not unify", 
            var_name, 
            var_type, 
            body_type
        ))
    }
}
//
//
pub fn type_check_fun(
    environment: &mut Environment<CicTerm, CicTerm>,
    fun_name: String,
    args: Vec<(String, CicTerm)>,
    out_type: CicTerm,
    body: CicTerm,
    is_rec: bool,
) -> Result<CicTerm, String> {
    let fun_type = make_multiarg_fun_type(&args, &out_type);
    let _ = type_check_type(&fun_type, environment);
    let mut assumptions = args;
    if is_rec {
        assumptions.push((fun_name.clone(), fun_type.clone()));
        //TODO possibly include necessary checks on recursive functions
    }

    let body_type = environment
        .with_local_declarations(&assumptions, |local_env| {
            Cic::type_check_term(body, local_env)
        })?;
    if !Cic::terms_unify(environment, &out_type, &body_type) {
        return Err(format!(
            "In {} definition, function type {:?} and body result {:?} are inconsistent",
            fun_name, out_type, body_type
        ));
    }

    environment.add_variable_to_context(&fun_name, &fun_type);
    Ok(CicTerm::Variable("Unit".to_string()))
}
//
//
pub fn type_check_axiom(
    environment: &mut Environment<CicTerm, CicTerm>,
    axiom_name: String,
    formula: CicTerm,
) -> Result<CicTerm, String> {
    let _ = Cic::type_check_term(formula.clone(), environment)?;
    environment.add_variable_to_context(&axiom_name, &formula);

    Ok(CicTerm::Variable("Unit".to_string()))
}
//
/// Given the values of an inductive type definition, returns the corresponding eliminator 
/// Reference that guided this implementation is Inductive Families by Peter Dybjer
fn inductive_eliminator(
    type_name: String,
    params: Vec<(String, CicTerm)>,
    ariety: CicTerm,
    constructors: Vec<(String, CicTerm)>,
) -> CicTerm {
    /// Creation of the first parameters ( A :: σ )
    fn make_left_param_vars(params: Vec<(String, CicTerm)>) -> Vec<CicTerm> {
        params
            .iter()
            .map(|(var_name, _)| Variable(var_name.to_owned()))
            .collect()
    }
    /// Creation of the first parameters ( a :: α\[A\] )
    fn make_right_param_vars(ariety: &CicTerm) -> Vec<CicTerm> {
        // TODO might need to rename right_params, i think they're all anonymous
        let right_params: Vec<CicTerm> = get_variables_as_terms(ariety);
        right_params
    }
    /// Creation of the full inductive type (P A a) instanciated
    fn make_instance_type(
        type_name: &str,
        left_param_vars: Vec<CicTerm>,
        right_param_vars: Vec<CicTerm>
    ) -> CicTerm {
        let instance_type = apply_arguments(&Variable(type_name.to_string()), left_param_vars);
        let instance_type = apply_arguments(&instance_type, right_param_vars);
        instance_type

    }
    /// Creation of the dependent result type of the eliminator
    /// ( C : (a :: α\[A\]) (c : P A a) set )
    fn make_result_type(type_name: &str, left_param_vars: Vec<CicTerm>, ariety: &CicTerm) -> CicTerm {
        // TODO might need to rename right_params, i think they're all anonymous
        let right_params = make_right_param_vars(ariety);
        let instance_type = make_instance_type(
            type_name, 
            left_param_vars, 
            right_params
        );

        clone_product_with_different_result(
            &ariety,
            Product(
                "instance".to_string(),
                Box::new(instance_type),
                //TODO review this sort
                Box::new(Sort("TYPE".to_string())),
            ),
        )
    }
    /// Creation of the dependent branches ( e :: ε\[A\] ) with each ε_j\[A\] is
    /// (b :: β\[A\]) (u :: γ\[A,b\]) (v :: δ\[A,b\]) C p\[A,b\] (cons_j A b u)
    /// where b are non recursive, u are recursive and v are inductive hypotesis and the output is 
    /// a construction of the result for this inductive case
    fn make_inductive_cases(
        constructors: Vec<(String, CicTerm)>,
        left_param_vars: Vec<CicTerm>,
        result_var: CicTerm,
        type_name: String
    ) -> Vec<CicTerm> {
        fn split_recursive_arguments(arg_types: Vec<CicTerm>, type_name: &str) -> (Vec<(String, CicTerm)>, Vec<(String, CicTerm)>) {
            let mut are_recursive = false;
            let mut recursive = vec![];
            let mut non_recursive = vec![];

            for (index, arg_type) in arg_types.into_iter().enumerate() {
                //TODO: switch to reference check instead of instance
                if is_instance_of(&arg_type, type_name) {
                    are_recursive = true;
                    recursive.push(((format!("r_{}", index)), arg_type));
                } else if are_recursive {
                    // TODO this could be an error case, should cover it?
                    println!("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");
                    println!("THE UNEXPECTED ERROR HAPPEND");
                } else {
                    non_recursive.push(((format!("nr_{}", index)), arg_type));
                }
            }

            (non_recursive, recursive)
        }
        fn make_inductive_hypotheses(rec_args: Vec<(String, CicTerm)>, result_var: CicTerm, left_params_len: usize) -> Vec<CicTerm> {
            let mut hypotheses = vec![];
            for (arg_name, arg_type) in rec_args {
                //assumption: arg_type is an instance (var/app) of the inductive type
                let mut right_params = application_args(arg_type);
                // drop left params used in instantiation of inductive type
                right_params.drain(0..left_params_len);  // da crab a drainer frfr
                let result_with_rights = apply_arguments(&result_var, right_params);

                hypotheses.push(Application(
                    Box::new(result_with_rights.clone()), 
                    Box::new(Variable(arg_name))
                ));
            }

            hypotheses
        }
        let left_params_len = left_param_vars.len();
        let mut cases: Vec<CicTerm> = vec![];

        for (constr_name, constr_type) in constructors {
            let innermost = get_prod_innermost(&constr_type);
            let mut right_params = application_args(innermost.clone());
            // drop left params used in instantiation of inductive type
            right_params.drain(0..left_params_len);  // da crab a drainer frfr
            let result_with_rights = apply_arguments(&result_var, right_params);
    
            // TODO might need to rename args, i think they're all anonymous
            // let args = get_variables_as_terms(&constr_type);
            let arg_types = get_arg_types(&constr_type);
            // in the paper non_recursive are called b and recursive u
            let (non_recursive, recursive) = split_recursive_arguments(arg_types, &type_name);
            let inductive_hypotheses = make_inductive_hypotheses(recursive.clone(), result_var.clone(), left_params_len);

            let constr_instance = apply_arguments(&Variable(constr_name), left_param_vars.clone());
            // let constr_instance = apply_arguments(constr_instance, right_params.clone());
            let constr_instance = apply_arguments(
                &constr_instance,
                simple_map(
                    non_recursive.clone(),
                    |(arg_name, _)| Variable(arg_name)
                )
            );
            let constr_instance = apply_arguments(
                &constr_instance, 
                simple_map(
                    recursive.clone(),
                    |(arg_name, _)| Variable(arg_name)
                )
            );
    
            let result_instance = apply_arguments(&result_with_rights, vec![constr_instance]);
    
            // parametrization of the full minor premise
            // start from the innermost (result_instance) and progressively wrap it 
            let named_hypotheses: Vec<(String, CicTerm)> = simple_map_indexed(
                inductive_hypotheses, 
                |(index, hypothesis)| {
                    (format!("ih_{}", index), hypothesis)
                }
            ); 
            let mut branch_type = make_multiarg_fun_type(
                &named_hypotheses,
                &result_instance
            );
            branch_type = make_multiarg_fun_type(
                &recursive,
                &branch_type
            );
            branch_type = make_multiarg_fun_type(
                &non_recursive,
                &branch_type
            );
    
            cases.push(branch_type);
        }
    
        cases
    }

    let left_param_vars = make_left_param_vars(params.clone());
    let result_var = Variable(format!("er_{}", type_name)); // er = eliminator result, C in the paper
    let result_type = make_result_type(&type_name, left_param_vars.clone(), &ariety);
    let inductive_cases = make_inductive_cases(
        constructors, 
        left_param_vars.clone(), 
        result_var.clone(),
        type_name.clone()
    );
    let right_params = simple_map_indexed(
        get_arg_types(&ariety),
        |(index, param_type)| {
            (format!("rp_{}", index), param_type)
        }
    );
    let right_param_vars = simple_map(
        right_params.clone(),
        |(param_name, _)| {
            Variable(param_name)
        }
    );
    let inductive_instace_var = Variable("t".to_string());
    let inductive_instace = make_instance_type(&type_name, left_param_vars, right_param_vars.clone());
    let mut result_instance = apply_arguments(&result_var, right_param_vars.clone());
    result_instance = Application(Box::new(result_instance), Box::new(inductive_instace_var));

    let mut full_parametrization = make_multiarg_fun_type(
        &vec![("t".to_string(), inductive_instace)], 
        &result_instance
    );
    full_parametrization = make_multiarg_fun_type(
        &right_params, 
        &full_parametrization
    );
    full_parametrization = make_multiarg_fun_type(
        &simple_map_indexed(
            inductive_cases,
            |(index, case_type)| {
                (format!("c_{}", index), case_type)
            }
        ), 
        &full_parametrization
    );
    full_parametrization = make_multiarg_fun_type(
        &vec![(format!("er_{}", type_name), result_type)], 
        &full_parametrization
    );
    full_parametrization = make_multiarg_fun_type(
        &params, 
        &full_parametrization
    );
    full_parametrization
}

fn update_context_inductive(
    environment: &mut Environment<CicTerm, CicTerm>,
    name: String,
    params: Vec<(String, CicTerm)>,
    ariety: CicTerm,
    constructors: Vec<(String, CicTerm)>,
) {
    //TODO make a record of the full constructor list for match type checking
    let ind_type = make_multiarg_fun_type(&params, &ariety);
    environment.add_variable_to_context(&name, &ind_type);
    for (constr_name, constr_type) in &constructors {
        environment.add_variable_to_context(constr_name, constr_type);
    }
    environment.add_variable_to_context(
        &format!("e_{}", name), 
        &inductive_eliminator(name, params, ariety, constructors)
    );
}

pub fn type_check_inductive(
    environment: &mut Environment<CicTerm, CicTerm>,
    type_name: String,
    params: Vec<(String, CicTerm)>,
    ariety: CicTerm,
    constructors: Vec<(String, CicTerm)>,
) -> Result<CicTerm, String> {
    //TODO check positivity
    let inductive_type = make_multiarg_fun_type(&params, &ariety);
    let inductive_type_sort =
        Cic::type_check_term(inductive_type.clone(), environment)?;
    let _ = check_is_sort(&inductive_type_sort)?;

    let inductive_assumptions: Vec<(String, CicTerm)> =
        vec![(type_name.clone(), inductive_type.clone())]
            .into_iter()
            .chain(params.clone().into_iter())
            .collect();

    let mut constr_bindings = vec![];
    environment.with_local_declarations(
        &inductive_assumptions,
        |local_env| {
            for (constr_name, constr_type) in constructors {
                let constr_type_sort =
                    Cic::type_check_term(constr_type.clone(), local_env)?;
                let _ = check_is_sort(&constr_type_sort)?;
                constr_bindings.push((constr_name, constr_type));
            }

            Ok::<(), String>(())
        },
    )?;

    update_context_inductive(
        environment,
        type_name,
        params, 
        ariety,
        constr_bindings,
    );
    Ok(CicTerm::Variable("Unit".to_string()))
}
//
//########################### STATEMENTS TYPE CHECKING
//
//########################### HELPER FUNCTIONS
//
/// Creates the CIC type of a function with named arguments `arg_types`
/// that returns a value of type `base`
fn make_multiarg_fun_type(
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
//
/// Checks that the given term is a sort. Return Ok if it is, Err otherwise
#[deprecated(note = "TODO: deprecated, callers should move to calling Cic::type_check_type instead")]
fn check_is_sort(term: &CicTerm) -> Result<(), String> {
    match term {
        CicTerm::Sort(_) => Ok(()),
        _ => Err(format!("Expected sort term, found: {:?}", term)),
    }
}
#[deprecated(note = "TODO: deprecated, callers should move to calling Cic::type_check_type instead")]
fn type_check_type(
    term: &CicTerm,
    environment: &mut Environment<CicTerm, CicTerm>,
) -> Result<CicTerm, String> {
    let term_type = Cic::type_check_term(term.clone(), environment)?;
    let _ = check_is_sort(&term_type);
    Ok(term_type)
}
//
//########################### HELPER FUNCTIONS
//
//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::cic::{
        cic::{Cic, CicTerm},
        cic::CicTerm::{Sort, Variable, Application, Product, Abstraction},
        cic::CicStm::{InductiveDef, Fun},
        type_check::{inductive_eliminator, type_check_fun, type_check_inductive},
    };
    use crate::type_theory::interface::TypeTheory;

    #[test]
    fn test_type_check_sort_n_vars() {
        let mut test_env = Cic::default_environment();
        test_env
            .add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
        // assumption, the type statement is included in the context
        test_env.add_variable_to_context(
            "n",
            &CicTerm::Variable("nat".to_string()),
        );
        // definition, we have the variabled and a typed body
        test_env.add_variable_definition(
            "m",
            &CicTerm::Variable("n".to_string()),
            &CicTerm::Variable("nat".to_string()),
        );

        // sorts
        assert_eq!(
            Cic::type_check_term(
                CicTerm::Sort("TYPE".to_string()),
                &mut test_env
            )
            .unwrap(),
            CicTerm::Sort("TYPE".to_string()),
            "Sort 'TYPE' type checking failed"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Sort("PROP".to_string()),
                &mut test_env
            )
            .is_ok(),
            "Sort 'PROP' type checking failed"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Sort("StupidInvalidSort".to_string()),
                &mut test_env
            )
            .is_err(),
            "Sort type checker accepts illegal sort"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Variable("TYPE".to_string()),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses sorts when used as variables"
        );

        // variables
        assert_eq!(
            Cic::type_check_term(
                CicTerm::Variable("n".to_string()),
                &mut test_env
            )
            .unwrap(),
            CicTerm::Variable("nat".to_string()),
            "Type checker refuses existing variable"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Variable("m".to_string()),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses defined variable"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Sort("stupidInvalidVar".to_string()),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts unbound variable"
        );
    }

    #[test]
    fn test_type_check_abstraction() {
        let mut test_env = Cic::default_environment();
        test_env
            .add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
        // assumption, the type statement is included in the context
        test_env.add_variable_to_context(
            "o",
            &CicTerm::Variable("nat".to_string()),
        );
        // function over nat
        test_env.add_variable_to_context(
            "s",
            &CicTerm::Product(
                "n".to_string(),
                Box::new(CicTerm::Variable("nat".to_string())),
                Box::new(CicTerm::Variable("nat".to_string())),
            ),
        );

        assert_eq!(
            Cic::type_check_term(
                CicTerm::Abstraction(
                    "x".to_string(),
                    Box::new(CicTerm::Variable("nat".to_string())),
                    Box::new(CicTerm::Variable("x".to_string())),
                ),
                &mut test_env
            )
            .unwrap(),
            CicTerm::Product(
                "x".to_string(),
                Box::new(CicTerm::Variable("nat".to_string())),
                Box::new(CicTerm::Variable("nat".to_string()))
            ),
            "Type checker refuses simple identity function"
        );
        assert_eq!(
            test_env.get_from_context("x"),
            None,
            "Abstraction type checker stains context with local variable"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Abstraction(
                    "x".to_string(),
                    Box::new(CicTerm::Variable("nat".to_string())),
                    Box::new(CicTerm::Application(
                        Box::new(CicTerm::Variable("s".to_string())),
                        Box::new(CicTerm::Variable("x".to_string())),
                    )),
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses function with more complex body"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Abstraction(
                    "x".to_string(),
                    Box::new(CicTerm::Variable(
                        "StupidInvalidType".to_string()
                    )),
                    Box::new(CicTerm::Variable("x".to_string())),
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts function defined over non existant type"
        );
    }

    #[test]
    fn test_type_check_product() {
        let mut test_env = Cic::default_environment();
        // polymorphic type constructor
        test_env.add_variable_to_context(
            "list",
            &CicTerm::Product(
                "T".to_string(),
                Box::new(CicTerm::Sort("TYPE".to_string())),
                Box::new(CicTerm::Sort("TYPE".to_string())),
            ),
        );

        assert_eq!(
            Cic::type_check_term(
                CicTerm::Product(
                    "T".to_string(),
                    Box::new(CicTerm::Sort("TYPE".to_string())),
                    Box::new(CicTerm::Variable("T".to_string())),
                ),
                &mut test_env
            )
            .unwrap(),
            CicTerm::Sort("TYPE".to_string()),
            "Type checker refuses simple polymorphic identity type"
        );
        assert_eq!(
            test_env.get_from_context("T"),
            None,
            "Product type checker stains context with local variable"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Product(
                    "T".to_string(),
                    Box::new(CicTerm::Sort("StupidInvalidSort".to_string())),
                    Box::new(CicTerm::Variable("T".to_string())),
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts polymorphic type over illegal sort"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Product(
                    "T".to_string(),
                    Box::new(CicTerm::Sort("TYPE".to_string())),
                    Box::new(CicTerm::Application(
                        Box::new(CicTerm::Variable("list".to_string())),
                        Box::new(CicTerm::Variable("T".to_string()))
                    ))
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses polymorphic types with more complex bodies"
        );
    }

    #[test]
    // TODO include tests for polymorphic types
    fn test_type_check_application() {
        let mut test_env = Cic::default_environment();
        test_env
            .add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
        // assumption, the type statement is included in the context
        test_env.add_variable_to_context(
            "n",
            &CicTerm::Variable("nat".to_string()),
        );
        // definition, we have the variabled and a typed body
        test_env.add_variable_definition(
            "m",
            &CicTerm::Variable("n".to_string()),
            &CicTerm::Variable("nat".to_string()),
        );
        // function over nat
        test_env.add_variable_to_context(
            "s",
            &CicTerm::Product(
                "n".to_string(),
                Box::new(CicTerm::Variable("nat".to_string())),
                Box::new(CicTerm::Variable("nat".to_string())),
            ),
        );

        assert_eq!(
            Cic::type_check_term(
                CicTerm::Application(
                    Box::new(CicTerm::Variable("s".to_string())),
                    Box::new(CicTerm::Variable("n".to_string())),
                ),
                &mut test_env
            )
            .unwrap(),
            CicTerm::Variable("nat".to_string()),
            "Type checker refuses function application over nat"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Application(
                    Box::new(CicTerm::Variable("s".to_string())),
                    Box::new(CicTerm::Variable("m".to_string())),
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker refuses function application over a variable when defined and not assumed"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Application(
                    Box::new(CicTerm::Variable("s".to_string())),
                    Box::new(CicTerm::Variable("TYPE".to_string())),
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts illegal function application"
        );
    }

    #[test]
    fn test_argument_dependent_function() {
        let mut test_env = Cic::default_environment();
        test_env
            .add_variable_to_context("Bool", &Sort("TYPE".to_string()));
        test_env
            .add_variable_to_context("true", &&Variable("Bool".to_string()));
        test_env
            .add_variable_to_context("Unit", &Sort("TYPE".to_string()));
        test_env
            .add_variable_to_context("it", &Variable("Unit".to_string()));
        test_env.add_variable_to_context(
            "if", 
            &Product(
                "T".to_string(), 
                Box::new(Sort("TYPE".to_string())), 
                Box::new(Product(
                    "exp".to_string(), 
                    Box::new(Variable("Bool".to_string())), 
                    Box::new(Product(
                        "ifTrue".to_string(), 
                        Box::new(Product(
                            "_".to_string(), 
                            Box::new(Variable("Unit".to_string())), 
                            Box::new(Variable("T".to_string())) 
                        )), 
                        Box::new(Variable("T".to_string())), 
                    )) 
                )) 
            )
        );

        assert!(
            Cic::type_check_term(
                Application(
                    Box::new(Application(
                        Box::new(Application(
                            Box::new(Variable("if".to_string())),
                            Box::new(Variable("Unit".to_string())),
                        )),
                        Box::new(Variable("true".to_string()))
                    )),
                    Box::new(Abstraction(
                        "_".to_string(), 
                        Box::new(Variable("Unit".to_string())),
                        Box::new(Variable("it".to_string())),
                    ))
                ),
                &mut test_env
            )
            .is_ok(),
            "Type checker refutes nested application when following argument types depend on previous"
        );
        assert!(
            Cic::type_check_stm(
                Fun(
                    "unifyResult".to_string(),
                    vec![("b".to_string(), Variable("Bool".to_string()))],
                    Box::new(Variable("Unit".to_string())),
                    Box::new(Application(
                        Box::new(Application(
                            Box::new(Application(
                                Box::new(Variable("if".to_string())),
                                Box::new(Variable("Unit".to_string())),
                            )),
                            Box::new(Variable("b".to_string()))
                        )),
                        Box::new(Abstraction(
                            "_".to_string(), 
                            Box::new(Variable("Unit".to_string())),
                            Box::new(Variable("it".to_string())),
                        ))
                    )),
                    false
                ),
                &mut test_env
            )
            .is_ok(), 
            "Type checker cant unify function output type with the result of a polymorphic expression"
        );
    }

    #[test]
    //TODO add check of exaustiveness of patterns
    fn test_type_check_match() {
        let mut test_env = Cic::default_environment();
        test_env
            .add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
        test_env.add_variable_to_context(
            "Bool",
            &CicTerm::Sort("TYPE".to_string()),
        );
        test_env.add_variable_to_context(
            "o",
            &CicTerm::Variable("nat".to_string()),
        );
        test_env.add_variable_to_context(
            "s",
            &CicTerm::Product(
                "_".to_string(),
                Box::new(CicTerm::Variable("nat".to_string())),
                Box::new(CicTerm::Variable("nat".to_string())),
            ),
        );
        test_env.add_variable_to_context(
            "c",
            &CicTerm::Variable("nat".to_string()),
        );
        test_env.add_variable_to_context(
            "true",
            &CicTerm::Variable("Bool".to_string()),
        );

        assert_eq!(
            Cic::type_check_term(
                CicTerm::Match(
                    Box::new(CicTerm::Variable("c".to_string())),
                    vec![
                        (
                            vec![CicTerm::Variable("o".to_string())],
                            CicTerm::Variable("o".to_string())
                        ),
                        (
                            vec![
                                CicTerm::Variable("s".to_string()),
                                CicTerm::Variable("n".to_string())
                            ],
                            CicTerm::Variable("c".to_string())
                        ),
                    ]
                ),
                &mut test_env
            )
            .unwrap(),
            CicTerm::Variable("nat".to_string()),
            "Type checker refuses matching over naturals"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Match(
                    Box::new(CicTerm::Variable(
                        "stupidUnboundVariable".to_string()
                    )),
                    vec![
                        (
                            vec![CicTerm::Variable("o".to_string())],
                            CicTerm::Variable("o".to_string())
                        ),
                        (
                            vec![
                                CicTerm::Variable("s".to_string()),
                                CicTerm::Variable("n".to_string())
                            ],
                            CicTerm::Variable("c".to_string())
                        ),
                    ]
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts matching over unbound variable"
        );
        assert!(
            Cic::type_check_term(
                CicTerm::Match(
                    Box::new(CicTerm::Variable("c".to_string())),
                    vec![
                        (
                            vec![CicTerm::Variable("o".to_string())],
                            CicTerm::Variable("o".to_string())
                        ),
                        (
                            vec![
                                CicTerm::Variable("s".to_string()),
                                CicTerm::Variable("n".to_string())
                            ],
                            CicTerm::Variable("true".to_string()) //this body has type : Bool
                        ),
                    ]
                ),
                &mut test_env
            )
            .is_err(),
            "Type checker accepts match with inconsistent branch types"
        );

        //TODO this should be address: do we want pattern variable to override names in context
        //or should the declared variables names be fresh?
        // assert!(
        //     Cic::type_check_term(
        //         CicTerm::Match(
        //             Box::new(CicTerm::Variable("c".to_string())),
        //             vec![
        //                 (
        //                     vec![CicTerm::Variable("c".to_string())], //random variable in place of constr
        //                     CicTerm::Variable("o".to_string())
        //                 ),
        //                 (
        //                     vec![
        //                         CicTerm::Variable("s".to_string()),
        //                         CicTerm::Variable("n".to_string())
        //                     ],
        //                     CicTerm::Variable("n".to_string())
        //                 ),
        //             ]
        //         ),
        //         &mut test_env
        //     )
        //     .is_err(),
        //     "Type checker accepts match with random (properly typed) variable in place of constructor"
        // );
    }

    //TODO add check for positivity
    #[test]
    fn test_type_check_inductive() {
        let mut test_env = Cic::default_environment();
        let constructors = vec![
            ("o".to_string(), Variable("nat".to_string())),
            (
                "s".to_string(),
                Product(
                    "_".to_string(),
                    Box::new(Variable("nat".to_string())),
                    Box::new(Variable("nat".to_string())),
                ),
            ),
        ];
        #[allow(non_snake_case)]
        let TYPE = Sort("TYPE".to_string());
        let ariety = TYPE.clone();

        // generic checks
        assert!(
            type_check_inductive(
                &mut test_env,
                "Empty".to_string(),
                vec![],
                TYPE.clone(),
                vec![]
            )
            .is_ok(),
            "Inductive type checking is refuting empty type"
        );
        assert!(
            type_check_inductive(
                &mut test_env,
                "inc".to_string(),
                vec![],
                TYPE.clone(),
                vec![
                    (
                        "correct".to_string(),
                        Variable("inc".to_string())
                    ),
                    (
                        "wrong".to_string(),
                        Variable("wrongType".to_string())
                    )
                ]
            )
            .is_err(),
            "Inductive type checking is accepting ill typed constructor"
        );
        assert!(
            type_check_inductive(
                &mut test_env,
                "fail".to_string(),
                vec![],
                Sort("UNBOUND_SORT".to_string()),
                vec![]
            )
            .is_err(),
            "Inductive type checking is accepting definition on non existent arieties"
        );
        assert!(
            test_env.with_local_declarations(&vec![
                ("nat".to_string(), TYPE.clone()),
                ("zero".to_string(), Variable("nat".to_string()))
            ], |local_env| {
                type_check_inductive(
                    local_env,
                    "fail".to_string(),
                    vec![],
                    Variable("zero".to_string()),  //bound, non-sort variable
                    vec![("cons".to_string(), Variable("zero".to_string()))]
                )
                .is_err()
            }),
            "Inductive type checking is accepting definition with simple term ariety"
        );
        assert!(
            test_env.with_local_declarations(&vec![
                ("nat".to_string(), TYPE.clone()),
                ("zero".to_string(), Variable("nat".to_string()))
            ], |local_env| {
                type_check_inductive(
                    local_env,
                    "fail".to_string(),
                    vec![],
                    TYPE.clone(),
                    vec![("cons".to_string(), Variable("zero".to_string()))]
                )
                .is_err()
            }),
            "Inductive type checking is accepting definition with simple term constructor type"
        );

        // peano naturals
        assert_eq!(
            type_check_inductive(
                &mut test_env,
                "nat".to_string(),
                vec![],
                ariety,
                constructors.clone()
            ),
            Ok(Variable("Unit".to_string())),
            "Inductive type checking isnt passing nat definition"
        );
        assert!(
            Cic::type_check_stm(
                InductiveDef(
                    "nat".to_string(),
                    vec![],
                    Box::new(TYPE.clone()),
                    constructors
                ),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support inductive definitions"
        );

        // logic relations
        assert!(
            type_check_inductive(
                &mut test_env,
                "Eq".to_string(),
                vec![
                    ("T".to_string(), TYPE.clone()),
                    ("x".to_string(), Variable("T".to_string()))
                ],
                CicTerm::Product(
                    "_".to_string(),
                    Box::new(CicTerm::Variable("T".to_string())),
                    Box::new(CicTerm::Sort("PROP".to_string()))
                ),
                vec![(
                    "refl".to_string(),
                    CicTerm::Application(
                        Box::new(CicTerm::Application(
                            Box::new(CicTerm::Application(
                                Box::new(CicTerm::Variable("Eq".to_string())),
                                Box::new(CicTerm::Variable("T".to_string()))
                            )),
                            Box::new(CicTerm::Variable("x".to_string()))
                        )),
                        Box::new(CicTerm::Variable("x".to_string()))
                    )
                )]
            )
            .is_ok(),
            "Inductive type checker doesnt accept equality definition"
        );

        // polymorphic lists
        let list_of_t = CicTerm::Application(
            Box::new(CicTerm::Variable("list".to_string())),
            Box::new(CicTerm::Variable("T".to_string())),
        );
        let constructors = vec![
            ("nil".to_string(), list_of_t.clone()),
            (
                "cons".to_string(),
                CicTerm::Product(
                    "_".to_string(),
                    Box::new(CicTerm::Variable("T".to_string())),
                    Box::new(CicTerm::Product(
                        "_".to_string(),
                        Box::new(list_of_t.clone()),
                        Box::new(list_of_t.clone()),
                    )),
                ),
            ),
        ];
        let wrong_constructors = vec![
            ("nil".to_string(), list_of_t.clone()),
            (
                "cons".to_string(),
                CicTerm::Product(
                    "_".to_string(),
                    Box::new(CicTerm::Variable("T_T".to_string())), //unbound variable
                    Box::new(CicTerm::Product(
                        "_".to_string(),
                        Box::new(list_of_t.clone()),
                        Box::new(list_of_t.clone()),
                    )),
                ),
            ),
        ];
        assert!(
            type_check_inductive(
                &mut test_env,
                "list".to_string(),
                vec![("T".to_string(), TYPE.clone())],
                TYPE.clone(),
                constructors
            )
            .is_ok(),
            "Inductive type checking isnt working with dependent inductive types"
        );
        assert!(
            type_check_inductive(
                &mut test_env,
                "list".to_string(),
                vec![("T".to_string(), TYPE.clone())],
                TYPE.clone(),
                wrong_constructors
            )
            .is_err(),
            "Inductive type checking isnt working with dependent inductive types"
        );
    }

    #[test]
    fn test_type_check_fun() {
        let mut test_env = Cic::default_environment();
        test_env
            .add_variable_to_context("Nat", &CicTerm::Sort("TYPE".to_string()));
        test_env.add_variable_to_context(
            "z",
            &CicTerm::Variable("Nat".to_string()),
        );
        test_env.add_variable_to_context(
            "s",
            &CicTerm::Product(
                "_".to_string(),
                Box::new(CicTerm::Variable("Nat".to_string())),
                Box::new(CicTerm::Variable("Nat".to_string())),
            ),
        );

        assert!(
            type_check_fun(
                &mut test_env,
                "f".to_string(),
                vec![("t".to_string(), CicTerm::Sort("TYPE".to_string()))],
                CicTerm::Sort("TYPE".to_string()),
                CicTerm::Variable("t".to_string()),
                false
            )
            .is_ok(),
            "Type checking refuses identity function"
        );

        let args = vec![
            ("n".to_string(), CicTerm::Variable("Nat".to_string())),
            ("m".to_string(), CicTerm::Variable("Nat".to_string())),
        ];
        let zerobranch = (
            //patter
            vec![CicTerm::Variable("z".to_string())],
            //body
            CicTerm::Variable("m".to_string()),
        );
        let succbranch = (
            //patter
            vec![
                CicTerm::Variable("s".to_string()),
                CicTerm::Variable("nn".to_string()),
            ],
            //body
            CicTerm::Application(
                Box::new(CicTerm::Variable("s".to_string())),
                Box::new(CicTerm::Application(
                    Box::new(CicTerm::Application(
                        Box::new(CicTerm::Variable("add".to_string())),
                        Box::new(CicTerm::Variable("nn".to_string())),
                    )),
                    Box::new(CicTerm::Variable("m".to_string())),
                )),
            ),
        );
        assert!(
            type_check_fun(
                &mut test_env,
                "add".to_string(),
                args.clone(),
                CicTerm::Sort("Nat".to_string()),
                CicTerm::Match(
                    Box::new(CicTerm::Variable("n".to_string())),
                    vec![zerobranch.clone(), succbranch.clone()]
                ),
                false
            )
            .is_err(),
            "Type checking accepts recursive function not marked as recursive"
        );
        let res = type_check_fun(
            &mut test_env,
            "add".to_string(),
            args,
            CicTerm::Variable("Nat".to_string()),
            CicTerm::Match(
                Box::new(CicTerm::Variable("n".to_string())),
                vec![zerobranch, succbranch],
            ),
            true,
        );
        assert!(
            res.is_ok(),
            "Type checking refuses recursive functions:\n{:?}",
            res.err()
        );

        assert!(
            type_check_fun(
                &mut test_env,
                "f".to_string(),
                vec![], 
                CicTerm::Variable("Nat".to_string()),
                CicTerm::Sort("TYPE".to_string()), 
                false
            ).is_err(),
            "Type checking accept function with a inconsistent declared and result type",
        );
    }

    #[test]
    fn test_inductive_eliminator() {
        // Unit
        assert_eq!(
            inductive_eliminator(
                "Unit".to_string(), 
                vec![], 
                Sort("TYPE".to_string()), 
                vec![("it".to_string(), Variable("Unit".to_string()))]
            ),

            Product(
                "er_Unit".to_string(), 
                Box::new(Product(
                    "instance".to_string(), 
                    Box::new(Variable("Unit".to_string())),
                    Box::new(Sort("TYPE".to_string())),
                )), 
                Box::new(
                    Product(
                        "c_0".to_string(), 
                        Box::new(Application(
                            Box::new(Variable("er_Unit".to_string())),
                            Box::new(Variable("it".to_string())),
                        )), 
                        Box::new(Product(
                            "t".to_string(), 
                            Box::new(Variable("Unit".to_string())),
                            Box::new(Application(
                                Box::new(Variable("er_Unit".to_string())),
                                Box::new(Variable("t".to_string())),
                            )),
                        ))
                    )
                )
            ),
        
            "Unit inductive eliminator not properly constructed"
        );
        // Bool
        assert_eq!(
            inductive_eliminator(
                "Bool".to_string(),
                vec![],
                Sort("TYPE".to_string()), 
                vec![
                    ("true".to_string(), Variable("Bool".to_string())),
                    ("false".to_string(), Variable("Bool".to_string()))
                ]
            ),

            Product(
                "er_Bool".to_string(), 
                Box::new(Product(
                    "instance".to_string(), 
                    Box::new(Variable("Bool".to_string())),
                    Box::new(Sort("TYPE".to_string())),
                )), 
                Box::new(
                    Product(
                        "c_0".to_string(), 
                        Box::new(Application(
                            Box::new(Variable("er_Bool".to_string())),
                            Box::new(Variable("true".to_string())),
                        )), 
                        Box::new(Product(
                            "c_1".to_string(), 
                            Box::new(Application(
                                Box::new(Variable("er_Bool".to_string())),
                                Box::new(Variable("false".to_string())),
                            )),
                            Box::new(Product(
                                "t".to_string(),
                                Box::new(Variable("Bool".to_string())),
                                Box::new(Application(
                                    Box::new(Variable("er_Bool".to_string())),
                                    Box::new(Variable("t".to_string())),
                                ))
                            ))
                        ))
                    )
                )
            ),

            "Boolean inductive eliminator not properly constructed"
        );
        // these next tests are copied straight from the examples in
        // Inductive Families (Dybjer) paper
        // Nat
        assert_eq!(
            inductive_eliminator(
                "Nat".to_string(),
                vec![],
                Sort("TYPE".to_string()), 
                vec![
                    ("z".to_string(), Variable("Nat".to_string())),
                    ("s".to_string(), Product(
                        "r_0".to_string(),
                        Box::new(Variable("Nat".to_string())), 
                        Box::new(Variable("Nat".to_string()))
                    ))
                ]
            ),

            Product(
                "er_Nat".to_string(), 
                Box::new(Product(
                    "instance".to_string(), 
                    Box::new(Variable("Nat".to_string())),
                    Box::new(Sort("TYPE".to_string())),
                )), 
                Box::new(
                    Product(
                        "c_0".to_string(), 
                        Box::new(Application(
                            Box::new(Variable("er_Nat".to_string())),
                            Box::new(Variable("z".to_string())),
                        )), 
                        Box::new(Product(
                            "c_1".to_string(),
                            Box::new(Product(
                                "r_0".to_string(),
                                Box::new(Variable("Nat".to_string())),
                                Box::new(Product(
                                    "ih_0".to_string(),
                                    Box::new(Application(
                                        Box::new(Variable("er_Nat".to_string())),
                                        Box::new(Variable("r_0".to_string()))
                                    )),
                                    Box::new(Application(
                                        Box::new(Variable("er_Nat".to_string())),
                                        Box::new(Application(
                                            Box::new(Variable("s".to_string())),
                                            Box::new(Variable("r_0".to_string()))
                                        ))
                                    ))
                                ))
                            )),
                            Box::new(Product(
                                "t".to_string(),
                                Box::new(Variable("Nat".to_string())),
                                Box::new(Application(
                                    Box::new(Variable("er_Nat".to_string())),
                                    Box::new(Variable("t".to_string()))
                                ))
                            ))
                        ))
                    )
                ),
            ),
            
            "Naturals inductive eliminator not properly constructed"
        );
        // List
        assert_eq!(
            inductive_eliminator(
                "List".to_string(),
                vec![("T".to_string(), Sort("TYPE".to_string()))],
                Sort("TYPE".to_string()), 
                vec![
                    ("nil".to_string(), Application(
                            Box::new(Variable("List".to_string())), 
                            Box::new(Variable("T".to_string()))
                    )),
                    ("cons".to_string(), Product(
                        "elem".to_string(), 
                        Box::new(Variable("T".to_string())), 
                        Box::new(Product(
                            "l".to_string(),
                            Box::new(Application(
                                Box::new(Variable("List".to_string())), 
                                Box::new(Variable("T".to_string()))
                            )), 
                            Box::new(Application(
                                Box::new(Variable("List".to_string())), 
                                Box::new(Variable("T".to_string()))
                            )) 
                        )) 
                    ))
                ]
            ),

            Product(
                "T".to_string(), 
                Box::new(Sort("TYPE".to_string())),
                Box::new(Product(
                    "er_List".to_string(),
                    Box::new(Product(
                        "instance".to_string(), 
                        Box::new(Application(
                            Box::new(Variable("List".to_string())), 
                            Box::new(Variable("T".to_string()))
                        )), 
                        Box::new(Sort("TYPE".to_string())) 
                    )),
                    Box::new(Product(
                        "c_0".to_string(), 
                        Box::new(Application(
                            Box::new(Variable("er_List".to_string())),
                            Box::new(Application(
                                Box::new(Variable("nil".to_string())), 
                                Box::new(Variable("T".to_string()))
                            )),
                        )),
                        Box::new(Product(
                            "c_1".to_string(),
                            Box::new(Product(
                                "nr_0".to_string(), 
                                Box::new(Variable("T".to_string())), 
                                Box::new(Product(
                                    "r_1".to_string(), 
                                    Box::new(Application(
                                        Box::new(Variable("List".to_string())), 
                                        Box::new(Variable("T".to_string()))
                                    )), 
                                    Box::new(Product(
                                        "ih_0".to_string(), 
                                        Box::new(Application(
                                            Box::new(Variable("er_List".to_string())), 
                                            Box::new(Variable("r_1".to_string()))
                                        )), 
                                        Box::new(Application(
                                            Box::new(Variable("er_List".to_string())), 
                                            Box::new(Application(
                                                Box::new(Application(
                                                    Box::new(Application(
                                                        Box::new(Variable("cons".to_string())), 
                                                        Box::new(Variable("T".to_string()))
                                                    )),
                                                    Box::new(Variable("nr_0".to_string()))
                                                )), 
                                                Box::new(Variable("r_1".to_string()))
                                            ))
                                        )) 
                                    )) 
                                )) 
                            )),
                            Box::new(Product(
                                "t".to_string(), 
                                Box::new(Application(
                                    Box::new(Variable("List".to_string())), 
                                    Box::new(Variable("T".to_string()))
                                )), 
                                Box::new(Application(
                                    Box::new(Variable("er_List".to_string())), 
                                    Box::new(Variable("t".to_string()))
                                )) 
                            ))
                        )), 
                    ))
                ))
            ),
            
            "List inductive eliminator not properly constructed"
        );
        // Vec
        assert_eq!(
            inductive_eliminator(
                "Vec".to_string(),
                vec![("T".to_string(), Sort("TYPE".to_string()))],
                Product(
                    "len".to_string(), 
                    Box::new(Variable("Nat".to_string())), 
                    Box::new(Sort("TYPE".to_string()))
                ), 
                vec![
                    ("nul".to_string(), Application(
                        Box::new(Application(
                            Box::new(Variable("Vec".to_string())), 
                            Box::new(Variable("T".to_string()))
                        )),
                        Box::new(Variable("z".to_string()))
                    )),
                    ("cons".to_string(), Product(
                        "nr_0".to_string(), 
                        Box::new(Variable("T".to_string())), 
                        Box::new(Product(
                            "nr_1".to_string(),
                            Box::new(Variable("Nat".to_string())), 
                            Box::new(Product(
                                "r_2".to_string(), 
                                Box::new(Application(
                                    Box::new(Application(
                                        Box::new(Variable("Vec".to_string())), 
                                        Box::new(Variable("T".to_string()))
                                    )),
                                    Box::new(Variable("nr_1".to_string()))
                                )), 
                                Box::new(Application(
                                    Box::new(Application(
                                        Box::new(Variable("Vec".to_string())), 
                                        Box::new(Variable("T".to_string()))
                                    )),
                                    Box::new(Application(
                                        Box::new(Variable("s".to_string())), 
                                        Box::new(Variable("nr_1".to_string()))
                                    ))
                                )) 
                            )) 
                        )) 
                    ))
                ]
            ),

            Product(
                "T".to_string(), 
                Box::new(Sort("TYPE".to_string())),
                Box::new(Product(
                    "er_Vec".to_string(),
                    Box::new(Product(
                        "len".to_string(),
                        Box::new(Variable("Nat".to_string())),
                        Box::new(Product(
                            "instance".to_string(), 
                            Box::new(Application(
                                Box::new(Application(
                                    Box::new(Variable("Vec".to_string())), 
                                    Box::new(Variable("T".to_string()))
                                )),
                                Box::new(Variable("len".to_string()))
                            )), 
                            Box::new(Sort("TYPE".to_string())) 
                        ))
                    )),
                    Box::new(Product(
                        "c_0".to_string(), 
                        Box::new(Application(
                            Box::new(Application(
                                Box::new(Variable("er_Vec".to_string())), 
                                Box::new(Variable("z".to_string()))
                            )),
                            Box::new(Application(
                                Box::new(Variable("nul".to_string())),
                                Box::new(Variable("T".to_string()))
                            ))
                        )),
                        Box::new(Product(
                            "c_1".to_string(),
                            Box::new(Product(
                                "nr_0".to_string(), 
                                Box::new(Variable("T".to_string())), 
                                Box::new(Product(
                                    "nr_1".to_string(),
                                    Box::new(Variable("Nat".to_string())),
                                    Box::new(Product(
                                        "r_2".to_string(), 
                                        Box::new(Application(
                                            Box::new(Application(
                                                Box::new(Variable("Vec".to_string())), 
                                                Box::new(Variable("T".to_string()))
                                            )),
                                            Box::new(Variable("nr_1".to_string()))
                                        )), 
                                        Box::new(Product(
                                            "ih_0".to_string(), 
                                            Box::new(Application(
                                                Box::new(Application(
                                                    Box::new(Variable("er_Vec".to_string())), 
                                                    Box::new(Variable("nr_1".to_string()))
                                                )),
                                                Box::new(Variable("r_2".to_string()))
                                            )), 
                                            Box::new(Application(
                                                Box::new(Application(
                                                    Box::new(Variable("er_Vec".to_string())), 
                                                    Box::new(Application(
                                                        Box::new(Variable("s".to_string())), 
                                                        Box::new(Variable("nr_1".to_string()))
                                                    ))
                                                )),
                                                Box::new(Application(
                                                    Box::new(Application(
                                                        Box::new(Application(
                                                            Box::new(Application(
                                                                Box::new(Variable("cons".to_string())),
                                                                Box::new(Variable("T".to_string()))
                                                            )),
                                                            Box::new(Variable("nr_0".to_string()))
                                                        )),
                                                        Box::new(Variable("nr_1".to_string()))
                                                    )),
                                                    Box::new(Variable("r_2".to_string()))
                                                ))
                                            )) 
                                        )) 
                                    ))
                                ))
                            )),
                            Box::new(Product(
                                "rp_0".to_string(),
                                Box::new(Variable("Nat".to_string())),
                                Box::new(Product(
                                    "t".to_string(), 
                                    Box::new(Application(
                                        Box::new(Application(
                                            Box::new(Variable("Vec".to_string())), 
                                            Box::new(Variable("T".to_string()))
                                        )),
                                        Box::new(Variable("rp_0".to_string()))
                                    )), 
                                    Box::new(Application(
                                        Box::new(Application(
                                            Box::new(Variable("er_Vec".to_string())), 
                                            Box::new(Variable("rp_0".to_string()))
                                        )),
                                        Box::new(Variable("t".to_string()))
                                    )) 
                                ))
                            ))
                        )), 
                    ))
                ))
            ),
            
            "Length-indexed vector inductive eliminator not properly constructed"
        );
    }
}

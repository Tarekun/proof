use super::cic::{Cic, CicTerm};
#[allow(unused_imports)]
use crate::type_theory::cic::cic::make_default_environment;
#[allow(unused_imports)]
use crate::type_theory::cic::cic::CicStm;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

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

fn check_is_sort(term: &CicTerm) -> Result<(), String> {
    match term {
        CicTerm::Sort(_) => Ok(()),
        _ => Err(format!("Expected sort term, found: {:?}", term)),
    }
}

fn type_check_type(
    term: &CicTerm,
    environment: &mut Environment<CicTerm, CicTerm>,
) -> Result<CicTerm, String> {
    let term_type = Cic::type_check_term(term.clone(), environment)?;
    let _ = check_is_sort(&term_type);
    Ok(term_type)
}

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
    let function_type = Cic::type_check_term(left.clone(), environment)?;
    let arg_type = Cic::type_check_term(right.clone(), environment)?;

    match function_type.clone() {
        CicTerm::Product(_, domain, codomain) => {
            if Cic::terms_unify(&(*domain), &arg_type) {
                Ok(*codomain)
            } else {
                println!("{}", format!("Checking {:?} {:?}", left, right));
                println!("{}", format!("with types {:?} {:?}", function_type, arg_type));
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
                    let mut typed_vars = type_constr_vars(&(*codomain), variables[1..].to_vec());
                    typed_vars.insert(0, (var_name.clone(), *(domain.clone())));
                    typed_vars
                }
                // i dont want to return results here
                _ => {panic!("Mismatch in number of variables for constructor");}
            }
            _ => {panic!(
                "Found illegal term in place of variable {:?}",
                variables[0],
            );}
        }
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
        if !Cic::terms_unify(&result_type, &matching_type) {
            return Err(
                format!(
                    "Pattern doesnt produce expected type: expected {:?} produced {:?}",
                    matching_type,
                    result_type
                )
            );
        }

        //body type checking
        let pattern_assumptions = type_constr_vars(&constr_type, pattern[1..].to_vec());
        let body_type = environment.with_local_declarations(&pattern_assumptions, |local_env| {
            Cic::type_check_term(body, local_env)
        })?;
        if return_type.is_none() {
            return_type = Some(body_type);
        } else if !Cic::terms_unify(&return_type.clone().unwrap(), &body_type) {
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
    var_type: CicTerm,
    body: CicTerm,
) -> Result<CicTerm, String> {
    let _ = type_check_type(&var_type, environment)?;
    let body_type = Cic::type_check_term(body.clone(), environment)?;

    if Cic::terms_unify(&body_type, &var_type) {
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
    let fun_type = make_multiarg_fun_type(&args, out_type);
    let mut assumptions = args;
    if is_rec {
        assumptions.push((fun_name, fun_type));
    }

    environment.with_local_declarations(
        &assumptions,
        |local_env| {
            Cic::type_check_term(body, local_env)
        },
    )?;

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
//
fn update_context_inductive(
    environment: &mut Environment<CicTerm, CicTerm>,
    name: String, 
    ind_type: CicTerm, 
    constructors: Vec<(String, CicTerm)>
) {
    //TODO also include eliminator
    //TODO make a record of the full constructor list for match type checking
    environment.add_variable_to_context(&name, &ind_type);
    for (constr_name, constr_type) in constructors {
        environment.add_variable_to_context(&constr_name, &constr_type);
    }
}
pub fn type_check_inductive(
    environment: &mut Environment<CicTerm, CicTerm>,
    type_name: String,
    params: Vec<(String, CicTerm)>,
    ariety: CicTerm,
    constructors: Vec<(String, CicTerm)>,
) -> Result<CicTerm, String> {
    //TODO check positivity
    let inductive_type = make_multiarg_fun_type(&params, ariety);
    let inductive_type_sort =
        Cic::type_check_term(inductive_type.clone(), environment)?;
    let _ = check_is_sort(&inductive_type_sort)?;

    let inductive_assumptions: Vec<(String, CicTerm)> =
        vec![(type_name.clone(), inductive_type.clone())]
            .into_iter()
            .chain(params.into_iter())
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

    update_context_inductive(environment, type_name, inductive_type, constr_bindings);
    Ok(CicTerm::Variable("Unit".to_string()))
}
//
//########################### STATEMENTS TYPE CHECKING
//
//
//########################### UNIT TESTS
#[test]
fn test_type_check_sort_n_vars() {
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    // assumption, the type statement is included in the context
    test_env
        .add_variable_to_context("n", &CicTerm::Variable("nat".to_string()));
    // definition, we have the variabled and a typed body
    test_env.add_variable_definition(
        "m",
        &CicTerm::Variable("n".to_string()),
        &CicTerm::Variable("nat".to_string()),
    );

    // sorts
    assert_eq!(
        Cic::type_check_term(CicTerm::Sort("TYPE".to_string()), &mut test_env)
            .unwrap(),
        CicTerm::Sort("TYPE".to_string()),
        "Sort 'TYPE' type checking failed"
    );
    assert!(
        Cic::type_check_term(CicTerm::Sort("PROP".to_string()), &mut test_env)
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
        Cic::type_check_term(CicTerm::Variable("TYPE".to_string()), &mut test_env)
            .is_ok(),
        "Type checker refuses sorts when used as variables"
    );

    // variables
    assert_eq!(
        Cic::type_check_term(CicTerm::Variable("n".to_string()), &mut test_env)
            .unwrap(),
        CicTerm::Variable("nat".to_string()),
        "Type checker refuses existing variable"
    );
    assert!(
        Cic::type_check_term(CicTerm::Variable("m".to_string()), &mut test_env)
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
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    // assumption, the type statement is included in the context
    test_env
        .add_variable_to_context("o", &CicTerm::Variable("nat".to_string()));
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
                Box::new(CicTerm::Variable("StupidInvalidType".to_string())),
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
    let mut test_env = make_default_environment();
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
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    // assumption, the type statement is included in the context
    test_env
        .add_variable_to_context("n", &CicTerm::Variable("nat".to_string()));
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
//TODO add check of exaustiveness of patterns
fn test_type_check_match() {
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    test_env
        .add_variable_to_context("o", &CicTerm::Variable("nat".to_string()));
    test_env.add_variable_to_context(
        "s",
        &CicTerm::Product(
            "_".to_string(),
            Box::new(CicTerm::Variable("nat".to_string())),
            Box::new(CicTerm::Variable("nat".to_string())),
        ),
    );
    test_env
        .add_variable_to_context("c", &CicTerm::Variable("nat".to_string()));
    test_env
        .add_variable_to_context("d", &CicTerm::Variable("TYPE".to_string()));

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
                        CicTerm::Variable("d".to_string()) //this body has type : TYPE
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
    let mut test_env = make_default_environment();
    let constructors = vec![
        ("o".to_string(), CicTerm::Variable("nat".to_string())),
        (
            "s".to_string(),
            CicTerm::Product(
                "_".to_string(),
                Box::new(CicTerm::Variable("nat".to_string())),
                Box::new(CicTerm::Variable("nat".to_string())),
            ),
        ),
    ];
    #[allow(non_snake_case)]
    let TYPE = CicTerm::Sort("TYPE".to_string());
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
                ("correct".to_string(), CicTerm::Variable("inc".to_string())),
                (
                    "wrong".to_string(),
                    CicTerm::Variable("wrongType".to_string())
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
            CicTerm::Sort("UNBOUND_SORT".to_string()),
            vec![]
        )
        .is_err(),
        "Inductive type checking is accepting definition on non existent arieties"
    );
    assert!(
        test_env.with_local_declarations(&vec![
            ("nat".to_string(), TYPE.clone()),
            ("zero".to_string(), CicTerm::Variable("nat".to_string()))
        ], |local_env| {
            type_check_inductive(
                local_env,
                "fail".to_string(),
                vec![],
                CicTerm::Variable("zero".to_string()),  //bound, non-sort variable
                vec![("cons".to_string(), CicTerm::Variable("zero".to_string()))]
            )
            .is_err()
        }),
        "Inductive type checking is accepting definition with simple term ariety"
    );
    assert!(
        test_env.with_local_declarations(&vec![
            ("nat".to_string(), TYPE.clone()),
            ("zero".to_string(), CicTerm::Variable("nat".to_string()))
        ], |local_env| {
            type_check_inductive(
                local_env,
                "fail".to_string(),
                vec![],
                TYPE.clone(),
                vec![("cons".to_string(), CicTerm::Variable("zero".to_string()))]
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
        Ok(CicTerm::Variable("Unit".to_string())),
        "Inductive type checking isnt passing nat definition"
    );
    assert!(
        Cic::type_check_stm(
            CicStm::InductiveDef(
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
                ("x".to_string(), CicTerm::Variable("T".to_string()))
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
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context("Nat", &CicTerm::Sort("TYPE".to_string()));
    test_env.add_variable_to_context("z", &CicTerm::Variable("Nat".to_string()));
    test_env.add_variable_to_context("s", 
        &CicTerm::Product(
            "_".to_string(),
            Box::new(CicTerm::Variable("Nat".to_string())), 
            Box::new(CicTerm::Variable("Nat".to_string()))
        )
    );

    assert!(
        type_check_fun(
            &mut test_env,
            "f".to_string(),
            vec![("t".to_string(), CicTerm::Sort("TYPE".to_string()))], 
            CicTerm::Sort("TYPE".to_string()),
            CicTerm::Variable("t".to_string()), 
            false
        ).is_ok(),
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
        CicTerm::Variable("m".to_string())
    );
    let succbranch = (
        //patter
        vec![CicTerm::Variable("s".to_string()), CicTerm::Variable("nn".to_string())], 
        //body
        CicTerm::Application(
            Box::new(CicTerm::Variable("s".to_string())), 
            Box::new(CicTerm::Application(
                    Box::new(CicTerm::Application(
                        Box::new(CicTerm::Variable("add".to_string())), 
                        Box::new(CicTerm::Variable("nn".to_string())), 
                    )),
                    Box::new(CicTerm::Variable("m".to_string())), 
                )
            )
        )
    );
    assert!(
        type_check_fun(
            &mut test_env,
            "add".to_string(),
            args.clone(), 
            CicTerm::Sort("Nat".to_string()),
            CicTerm::Match(
                Box::new(CicTerm::Variable("n".to_string())), 
                vec![zerobranch.clone(),succbranch.clone()]
            ), 
            false 
        ).is_err(),
        "Type checking accepts recursive function not marked as recursive"
    );
    let res = type_check_fun(
        &mut test_env,
        "add".to_string(),
        args, 
        CicTerm::Variable("Nat".to_string()),
        CicTerm::Match(
            Box::new(CicTerm::Variable("n".to_string())), 
            vec![zerobranch,succbranch,]
        ), 
        true 
    );
    assert!(
        res.is_ok(),
        "Type checking refuses recursive functions:\n{:?}",
        res.err()
    );
}
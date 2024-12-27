use crate::{
    parsing::Expression,
    type_theory::{
        cic::{
            cic::{make_default_environment, Cic, CicTerm},
            evaluation::{
                evaluate_abstraction, evaluate_application, evaluate_let,
                evaluate_type_product, evaluate_var,
            },
        },
        environment::Environment,
        interface::TypeTheory,
    },
};
//TODO oltre al fix di questo test, bisogna accertarsi che le funzioni
//falliscano in casi degeneri
#[test]
fn test_var_evaluation() {
    let test_var_name = "test_var";
    let test_var_type = SystemFTerm::Sort("TYPE".to_string());
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context(test_var_name, &test_var_type);

    assert_eq!(
        evaluate_var(&test_env, &test_var_name),
        (
            SystemFTerm::Variable(test_var_name.to_string()),
            test_var_type.clone()
        ),
        "Variable term not properly constructed"
    );
    // assert_eq!(
    //     evaluate_var(&test_env, "TYPE"),
    //     (
    //         SystemFTerm::Sort("TYPE".to_string()),
    //         SystemFTerm::Sort("TYPE".to_string())
    //     ),
    //     "Sort name returns a simple variable instead of a sort term"
    // );
    assert_eq!(
        Cic::evaluate_expression(
            Expression::VarUse(test_var_name.to_string()),
            &mut test_env,
        ),
        (
            SystemFTerm::Variable(test_var_name.to_string()),
            test_var_type
        ),
        "Top level evaluation doesnt work with variables as expected"
    );

    let var_term = elaborate_var(test_var_name.to_string());
    assert_eq!(
        var_term,
        CicTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    // assert_eq!(var_type, test_var_type, "Variable type mismatch");
    let var_term = Cic::elaborate_expression(Expression::VarUse(
        test_var_name.to_string(),
    ));
    assert_eq!(
        var_term,
        CicTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    // assert_eq!(var_type, test_var_type, "Variable type mismatch");
}

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
        Cic::type_check(CicTerm::Sort("TYPE".to_string()), &mut test_env)
            .unwrap(),
        CicTerm::Sort("TYPE".to_string()),
        "Sort 'TYPE' type checking failed"
    );
    assert!(
        Cic::type_check(CicTerm::Sort("PROP".to_string()), &mut test_env)
            .is_ok(),
        "Sort 'PROP' type checking failed"
    );
    assert!(
        Cic::type_check(
            CicTerm::Sort("StupidInvalidSort".to_string()),
            &mut test_env
        )
        .is_err(),
        "Sort type checker accepts illegal sort"
    );
    assert!(
        Cic::type_check(CicTerm::Variable("TYPE".to_string()), &mut test_env)
            .is_ok(),
        "Type checker refuses sorts when used as variables"
    );

    // variables
    assert_eq!(
        Cic::type_check(CicTerm::Variable("n".to_string()), &mut test_env)
            .unwrap(),
        CicTerm::Variable("nat".to_string()),
        "Type checker refuses existing variable"
    );
    assert!(
        Cic::type_check(CicTerm::Variable("m".to_string()), &mut test_env)
            .is_ok(),
        "Type checker refuses defined variable"
    );
    assert!(
        Cic::type_check(
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
        Cic::type_check(
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
    assert!(
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
    assert!(
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
    // assert!(
    //     type_check(
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

#[test]
fn test_abs_evaluation() {
    let mut test_env = make_default_environment();
    let expected_term = SystemFTerm::Abstraction(
        "x".to_string(),
        Box::new(SystemFTerm::Sort("TYPE".to_string())),
        Box::new(SystemFTerm::Variable("x".to_string())),
    );
    let expected_type = SystemFTerm::Product(
        "_".to_string(),
        Box::new(SystemFTerm::Sort("TYPE".to_string())),
        Box::new(SystemFTerm::Sort("TYPE".to_string())),
    );

    // assert_eq!(
    //     evaluate_abstraction(
    //         &mut test_env,
    //         "x".to_string(),
    //         Expression::VarUse("TYPE".to_string()),
    //         Expression::VarUse("x".to_string())
    //     ),
    //     (expected_term.clone(), expected_type.clone()),
    //     "Abstraction evaluation isnt working as expected"
    // );
    // assert_eq!(
    //     Cic::evaluate_expression(
    //         Expression::Abstraction(
    //             "x".to_string(),
    //             Box::new(Expression::VarUse("TYPE".to_string())),
    //             Box::new(Expression::VarUse("x".to_string())),
    //         ),
    //         &mut test_env,
    //     ),
    //     (expected_term, expected_type),
    //     "Top level evaluator isnt working with abstraction"
    // );
}

#[test]
fn test_prod_evaluation() {
    let mut test_env = make_default_environment();
    let expected_term = SystemFTerm::Product(
        "x".to_string(),
        Box::new(SystemFTerm::Sort("TYPE".to_string())),
        Box::new(SystemFTerm::Sort("TYPE".to_string())),
    );
    let expected_type = SystemFTerm::Sort("TYPE".to_string());

    // assert_eq!(
    //     evaluate_type_product(
    //         &mut test_env,
    //         "x".to_string(),
    //         Expression::VarUse("TYPE".to_string()),
    //         Expression::VarUse("TYPE".to_string())
    //     ),
    //     (expected_term.clone(), expected_type.clone()),
    //     "Type abstraction evaluation isnt working as expected"
    // );
    // assert_eq!(
    //     Cic::evaluate_expression(
    //         Expression::TypeProduct(
    //             "x".to_string(),
    //             Box::new(Expression::VarUse("TYPE".to_string())),
    //             Box::new(Expression::VarUse("TYPE".to_string())),
    //         ),
    //         &mut test_env,
    //     ),
    //     (expected_term, expected_type),
    //     "Top level evaluator isnt working with type abstraction"
    // );
}

#[test]
fn test_app_evaluation() {
    let mut test_env = make_default_environment();
    test_env
        .add_variable_to_context("nat", &SystemFTerm::Sort("TYPE".to_string()));
    test_env.add_variable_to_context(
        "o",
        &SystemFTerm::Variable("nat".to_string()),
    );
    test_env.add_variable_to_context(
        "s",
        &SystemFTerm::Product(
            "_".to_string(),
            Box::new(SystemFTerm::Variable("nat".to_string())),
            Box::new(SystemFTerm::Variable("nat".to_string())),
        ),
    );
    let expected_term = SystemFTerm::Application(
        Box::new(SystemFTerm::Variable("s".to_string())),
        Box::new(SystemFTerm::Variable("o".to_string())),
    );
    let expected_type = SystemFTerm::Variable("nat".to_string());

    assert_eq!(
        evaluate_application(
            &mut test_env,
            Expression::VarUse("s".to_string()),
            Expression::VarUse("o".to_string())
        ),
        (expected_term.clone(), expected_type.clone()),
        "Application evaluation isnt working as expected"
    );
    assert_eq!(
        Cic::evaluate_expression(
            Expression::Application(
                Box::new(Expression::VarUse("s".to_string())),
                Box::new(Expression::VarUse("o".to_string())),
            ),
            &mut test_env,
        ),
        (expected_term, expected_type),
        "Top level evaluator isnt working with applications"
    );
}

#[test]
fn test_let_evaluation() {
    let mut test_env = make_default_environment();
    test_env
        .add_variable_to_context("nat", &SystemFTerm::Sort("TYPE".to_string()));
    test_env.add_variable_to_context(
        "c",
        &SystemFTerm::Variable("nat".to_string()),
    );
    let expected_term = SystemFTerm::Variable("n".to_string());
    let expected_type = SystemFTerm::Variable("nat".to_string());

    assert_eq!(
        evaluate_let(
            &mut test_env,
            "n".to_string(),
            Expression::VarUse("c".to_string()),
        ),
        (expected_term.clone(), expected_type.clone()),
        "Let definition evaluation isnt working as expected"
    );
    assert_eq!(
        Cic::evaluate_expression(
            Expression::Let(
                "n".to_string(),
                Box::new(Expression::VarUse("c".to_string())),
            ),
            &mut test_env,
        ),
        (expected_term, expected_type),
        "Top level evaluator isnt working with let definitions"
    );
}

#[test]
fn test_match_evaluation() {}

#[test]
fn test_inductive_evaluation() {}

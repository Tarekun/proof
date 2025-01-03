use crate::{
    parsing::{Expression, Statement},
    type_theory::{
        cic::{
            cic::{make_default_environment, Cic, CicTerm},
            elaboration::{
                elaborate_abstraction, elaborate_application, elaborate_let,
                elaborate_match, elaborate_type_product, elaborate_var_use,
            },
        },
        environment::Environment,
        interface::TypeTheory,
    },
};

use super::elaboration::elaborate_inductive;

//########################## ELABORATION TESTS
#[test]
fn test_var_elaboration() {
    let test_var_name = "test_var";

    assert_eq!(
        elaborate_var_use(test_var_name.to_string()),
        CicTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    assert_eq!(
        elaborate_var_use("TYPE".to_string()),
        CicTerm::Sort("TYPE".to_string()),
        "Sort name returns a simple variable instead of a sort term"
    );
    assert_eq!(
        Cic::elaborate_expression(Expression::VarUse(
            test_var_name.to_string()
        ),),
        CicTerm::Variable(test_var_name.to_string()),
        "Top level elaboration doesnt work with variables as expected"
    );
}

#[test]
fn test_abs_elaboration() {
    let expected_term = CicTerm::Abstraction(
        "x".to_string(),
        Box::new(CicTerm::Sort("TYPE".to_string())),
        Box::new(CicTerm::Variable("x".to_string())),
    );

    assert_eq!(
        elaborate_abstraction(
            "x".to_string(),
            Expression::VarUse("TYPE".to_string()),
            Expression::VarUse("x".to_string())
        ),
        expected_term.clone(),
        "Abstraction elaboration isnt working as expected"
    );
    assert_eq!(
        Cic::elaborate_expression(Expression::Abstraction(
            "x".to_string(),
            Box::new(Expression::VarUse("TYPE".to_string())),
            Box::new(Expression::VarUse("x".to_string())),
        ),),
        expected_term,
        "Top level elaborator isnt working with abstraction"
    );
}

#[test]
fn test_prod_elaboration() {
    let expected_term = CicTerm::Product(
        "x".to_string(),
        Box::new(CicTerm::Sort("TYPE".to_string())),
        Box::new(CicTerm::Sort("TYPE".to_string())),
    );

    assert_eq!(
        elaborate_type_product(
            "x".to_string(),
            Expression::VarUse("TYPE".to_string()),
            Expression::VarUse("TYPE".to_string())
        ),
        expected_term.clone(),
        "Type abstraction elaboration isnt working as expected"
    );
    assert_eq!(
        Cic::elaborate_expression(Expression::TypeProduct(
            "x".to_string(),
            Box::new(Expression::VarUse("TYPE".to_string())),
            Box::new(Expression::VarUse("TYPE".to_string())),
        ),),
        expected_term,
        "Top level elaborator isnt working with type abstraction"
    );
}

#[test]
fn test_app_elaboration() {
    let expected_term = CicTerm::Application(
        Box::new(CicTerm::Variable("s".to_string())),
        Box::new(CicTerm::Variable("o".to_string())),
    );

    assert_eq!(
        elaborate_application(
            Expression::VarUse("s".to_string()),
            Expression::VarUse("o".to_string())
        ),
        expected_term.clone(),
        "Application elaboration isnt working as expected"
    );
    assert_eq!(
        Cic::elaborate_expression(Expression::Application(
            Box::new(Expression::VarUse("s".to_string())),
            Box::new(Expression::VarUse("o".to_string())),
        ),),
        expected_term,
        "Top level elaborator isnt working with applications"
    );
}

#[test]
fn test_match_elaboration() {
    let expected_term = CicTerm::Match(
        Box::new(CicTerm::Variable("t".to_string())),
        vec![
            (
                vec![CicTerm::Variable("o".to_string())],
                CicTerm::Application(
                    Box::new(CicTerm::Variable("s".to_string())),
                    Box::new(CicTerm::Variable("o".to_string())),
                ),
            ),
            (
                vec![
                    CicTerm::Variable("s".to_string()),
                    CicTerm::Variable("n".to_string()),
                ],
                CicTerm::Variable("n".to_string()),
            ),
        ],
    );
    let base_pattern = (
        vec![Expression::VarUse("o".to_string())],
        Expression::Application(
            Box::new(Expression::VarUse("s".to_string())),
            Box::new(Expression::VarUse("o".to_string())),
        ),
    );
    let inductive_patter = (
        vec![
            Expression::VarUse("s".to_string()),
            Expression::VarUse("n".to_string()),
        ],
        Expression::VarUse("n".to_string()),
    );

    assert_eq!(
        elaborate_match(
            Expression::VarUse("t".to_string()),
            vec![base_pattern.clone(), inductive_patter.clone()]
        ),
        expected_term,
        "Match elaboration isnt working as expected"
    );
    assert_eq!(
        Cic::elaborate_expression(Expression::Match(
            Box::new(Expression::VarUse("t".to_string())),
            vec![base_pattern, inductive_patter]
        )),
        expected_term,
        "Top level elaboration doesnt work with match"
    );
}

#[test]
fn test_let_elaboration() {
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    test_env
        .add_variable_to_context("c", &CicTerm::Variable("nat".to_string()));
    let expected_body = CicTerm::Variable("c".to_string());
    let expected_type = CicTerm::Variable("nat".to_string());

    elaborate_let(
        &mut test_env,
        "n".to_string(),
        Expression::VarUse("nat".to_string()),
        Expression::VarUse("c".to_string()),
    );
    assert_eq!(
        test_env.get_from_deltas("n"),
        Some(("n", &(expected_body.clone(), expected_type.clone()))),
        "Let definition elaboration isnt working as expected"
    );

    elaborate_let(
        &mut test_env,
        "m".to_string(),
        Expression::VarUse("nat".to_string()),
        Expression::VarUse("c".to_string()),
    );
    assert_eq!(
        test_env.get_from_deltas("m"),
        Some(("m", &(expected_body.clone(), expected_type.clone()))),
        "Top level elaboration isnt working with let"
    );
}

#[test]
fn test_inductive_elaboration() {
    let mut test_env = make_default_environment();
    let expected_nat = CicTerm::Variable("nat".to_string());
    let _expected_zero = CicTerm::Variable("o".to_string());
    let _expected_succ = CicTerm::Variable("s".to_string());
    let expected_succ_type = CicTerm::Product(
        "_".to_string(),
        Box::new(CicTerm::Variable("nat".to_string())),
        Box::new(CicTerm::Variable("nat".to_string())),
    );

    elaborate_inductive(
        &mut test_env,
        "nat".to_string(),
        vec![
            ("o".to_string(), vec![]),
            ("s".to_string(), vec![Expression::VarUse("nat".to_string())]),
        ],
    );
    assert_eq!(
        test_env.get_from_context("o"),
        Some(("o", &expected_nat)),
        "Inductive elaboration isnt working with constant constructor"
    );
    assert_eq!(
        test_env.get_from_context("s"),
        Some(("s", &expected_succ_type)),
        "Inductive elaboration isnt working with unary constructor"
    );

    Cic::elaborate_statement(
        Statement::Inductive(
            "peano".to_string(),
            vec![
                ("zero".to_string(), vec![]),
                (
                    "successor".to_string(),
                    vec![(
                        "n".to_string(),
                        Expression::VarUse("nat".to_string()),
                    )],
                ),
            ],
        ),
        &mut test_env,
    );
    assert_eq!(
        test_env.get_from_context("zero"),
        Some(("zero", &CicTerm::Variable("nat".to_string()))),
        "Top level evaluator doesnt support inductive elaboration"
    );
}
//########################## ELABORATION TESTS

//########################## TYPE CHECK TESTS
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
    assert_eq!(
        test_env.get_from_context("x"),
        None,
        "Abstraction type checker stains context with local variable"
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
    assert_eq!(
        test_env.get_from_context("T"),
        None,
        "Product type checker stains context with local variable"
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
    assert!(
        Cic::type_check(
            CicTerm::Match(
                Box::new(CicTerm::Variable("c".to_string())),
                vec![
                    (
                        vec![CicTerm::Variable("c".to_string())], //random variable in place of constr
                        CicTerm::Variable("o".to_string())
                    ),
                    (
                        vec![
                            CicTerm::Variable("s".to_string()),
                            CicTerm::Variable("n".to_string())
                        ],
                        CicTerm::Variable("n".to_string())
                    ),
                ]
            ),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts match with random (properly typed) variable in place of constructor"
    );
}
//########################## TYPE CHECK TESTS

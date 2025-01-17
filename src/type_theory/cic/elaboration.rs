use super::cic::CicTerm;
use crate::parser::api::{Expression, NsAst};
#[allow(unused_imports)]
use crate::type_theory::cic::cic::make_default_environment;
use crate::type_theory::interface::TypeTheory;
use crate::type_theory::{cic::cic::Cic, environment::Environment};

fn map_typed_variables(
    variables: &Vec<(String, Expression)>,
) -> Vec<(String, CicTerm)> {
    variables
        .iter()
        .map(|(var_name, var_type_exp)| {
            (
                var_name.to_owned(),
                Cic::elaborate_expression(var_type_exp.to_owned()),
            )
        })
        .collect()
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

pub fn elaborate_arrow(domain: Expression, codomain: Expression) -> CicTerm {
    let type_term = Cic::elaborate_expression(domain);
    let body_term = Cic::elaborate_expression(codomain);

    CicTerm::Product("_".to_string(), Box::new(type_term), Box::new(body_term))
}

pub fn elaborate_inductive(
    type_name: String,
    parameters: Vec<(String, Expression)>,
    ariety: Expression,
    constructors: Vec<(String, Expression)>,
) -> CicTerm {
    let parameter_terms: Vec<(String, CicTerm)> =
        map_typed_variables(&parameters);
    let ariety_term: CicTerm = Cic::elaborate_expression(ariety);
    let constructor_terms: Vec<(String, CicTerm)> = constructors
        .iter()
        .map(|(constr_name, constr_type)| {
            (
                constr_name.to_owned(),
                Cic::elaborate_expression(constr_type.to_owned()),
            )
        })
        .collect();

    CicTerm::InductiveDef(
        type_name,
        parameter_terms,
        Box::new(ariety_term),
        constructor_terms,
    )
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

    if Cic::unifies(&assigned_type, &var_type_term) {
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

    let _ = elaborate_let(
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

    let _ = elaborate_let(
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
    let ariety = Expression::VarUse("TYPE".to_string());

    assert_eq!(
        elaborate_inductive(
            "nat".to_string(),
            vec![],
            ariety.clone(),
            vec![
                ("o".to_string(), Expression::VarUse("nat".to_string())),
                (
                    "s".to_string(),
                    Expression::TypeProduct(
                        "_".to_string(),
                        Box::new(Expression::VarUse("nat".to_string())),
                        Box::new(Expression::VarUse("nat".to_string())),
                    ),
                ),
            ],
        ),
        CicTerm::InductiveDef(
            "nat".to_string(),
            vec![],
            Box::new(CicTerm::Sort("TYPE".to_string())),
            vec![
                ("o".to_string(), CicTerm::Variable("nat".to_string())),
                (
                    "s".to_string(),
                    CicTerm::Product(
                        "_".to_string(),
                        Box::new(CicTerm::Variable("nat".to_string())),
                        Box::new(CicTerm::Variable("nat".to_string())),
                    )
                )
            ]
        ),
        "Inductive elaboration isnt working with constant constructor"
    );
}

use super::fol::FolStm::{Axiom, Fun, Let};
use super::fol::FolTerm::{Abstraction, Variable};
use super::fol::FolType::{Arrow, Atomic, ForAll};
use super::fol::{Fol, FolStm, FolTerm, FolType};
use crate::parser::api::Statement;
use crate::{
    misc::Union,
    parser::api::{Expression, NsAst},
    runtime::program::Program,
};
use regex::Regex;

fn map_typed_variables(
    variables: &Vec<(String, Expression)>,
) -> Vec<(String, FolType)> {
    variables
        .iter()
        .map(|(var_name, var_type_exp)| {
            match Fol::elaborate_expression(var_type_exp.clone()) {
                Union::L(term) => panic!(
                    "TODO handle this but term is no supposed to show up {:?}",
                    term
                ),
                Union::R(var_type) => (var_name.to_owned(), var_type),
            }
        })
        .collect()
}

fn type_expected_error(task: &str, term: &FolTerm) -> Result<(), String> {
    Err(format!(
        "[FOL elaboration]: in {} a type was expected, but term {:?} was received",
        task,
        term
    ))
}
fn term_expected_error(task: &str, type_exp: &FolType) -> Result<(), String> {
    Err(format!(
        "[FOL elaboration]: in {} a term was expected, but type {:?} was received",
        task,
        type_exp
    ))
}

//########################### EXPRESSIONS ELABORATION
//
pub fn elaborate_var_use(var_name: String) -> Union<FolTerm, FolType> {
    let pascal_case = Regex::new(r"^[A-Z][a-zA-Z]*$").unwrap();

    //TODO better evaluate how to distinguish them
    //for now the logic is if it's spelled in PascalCase, its a type (formula)
    if pascal_case.is_match(&var_name) {
        Union::R(Atomic(var_name))
    } else {
        Union::L(Variable(var_name))
    }
}
//
//
pub fn elaborate_abstraction(
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> Result<FolTerm, String> {
    match Fol::elaborate_expression(var_type) {
        Union::R(var_type) => match Fol::elaborate_expression(body) {
            Union::L(body_term) => Ok(Abstraction(var_name.clone(), Box::new(var_type), Box::new(body_term))),
            Union::R(wrong_type) => Err(format!(
                "FOL abstraction expects a term as a body, not type {:?}", 
                wrong_type
            )),
        }
        Union::L(term) => Err(format!(
            "FOL abstraction expects a type as variable judgement, not term {:?}", 
            term
        )),
    }
}
//
//
pub fn elaborate_arrow(
    domain: Expression,
    codomain: Expression,
) -> Result<FolType, String> {
    match Fol::elaborate_expression(domain) {
        Union::R(domain_type) => match Fol::elaborate_expression(codomain) {
            Union::R(codomain_type) => {
                Ok(Arrow(Box::new(domain_type), Box::new(codomain_type)))
            }
            Union::L(term) => Err(format!(
                "FOL arrow type can only be composed of subtypes, not term {:?}", 
                term
            )),
        },
        Union::L(term) => Err(format!(
            "FOL arrow type can only be composed of subtypes, not term {:?}", 
            term
        )),
    }
}
//
//
pub fn elaborate_application(
    left: Expression,
    right: Expression,
) -> Result<FolTerm, String> {
    match Fol::elaborate_expression(left) {
        Union::L(function) => match Fol::elaborate_expression(right) {
            Union::L(argument) => {
                Ok(FolTerm::Application(Box::new(function), Box::new(argument)))
            }
            Union::R(wrong_type) => Err(format!(
                "FOL application expects a term as a argument, not type {:?}",
                wrong_type
            )),
        },
        Union::R(wrong_type) => Err(format!(
            "FOL application expects a term as a function, not type {:?}",
            wrong_type
        )),
    }
}
//
//
pub fn elaborate_forall(
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> Result<FolType, String> {
    match Fol::elaborate_expression(var_type) {
        Union::R(var_type) => match Fol::elaborate_expression(body) {
            Union::R(body_formula) => Ok(ForAll(
                var_name.clone(),
                Box::new(var_type),
                Box::new(body_formula),
            )),
            Union::L(term) => Err(format!(
                "FOL forall expects a type as body formula, not term {:?}",
                term
            )),
        },
        Union::L(term) => Err(format!(
            "FOL forall expects a type as variable judgement, not term {:?}",
            term
        )),
    }
}
//
//########################### EXPRESSIONS ELABORATION
//
//########################### STATEMENTS ELABORATION
//
fn elaborate_ast_vector(
    program: &mut Program<FolTerm, FolStm>,
    root: String,
    asts: Vec<NsAst>,
) -> Result<(), String> {
    let mut errors: Vec<_> = vec![];

    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(stm) => {
                match Fol::elaborate_statement(stm.clone(), program) {
                    Err(message) => errors.push(message),
                    Ok(_) => {}
                }
            }
            NsAst::Exp(exp) => match Fol::elaborate_expression(exp) {
                Union::L(term) => program.push_term(&term),
                // drop top level type expressions as they are not reducable in LOF
                // TODO revaluate this implementation
                Union::R(_type_exp) => {}
            },
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "Elaborating the ASTs rooted at '{}' raised errors:\n{}",
            root,
            errors.join("\n")
        ))
    }
}
pub fn elaborate_file_root(
    program: &mut Program<FolTerm, FolStm>,
    file_path: String,
    asts: Vec<NsAst>,
) -> Result<(), String> {
    elaborate_ast_vector(program, file_path, asts)
}
//
//
pub fn elaborate_dir_root(
    program: &mut Program<FolTerm, FolStm>,
    dir_path: String,
    asts: Vec<NsAst>,
) -> Result<(), String> {
    // elaborate_ast_vector(program, dir_path, asts);
    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(Statement::FileRoot(file_path, file_contet)) => {
                let _ = elaborate_file_root(
                    program,
                    format!("{}/{}", dir_path, file_path),
                    file_contet,
                );
            }
            _ => {
                return Err(format!("AST nodes of directory node can only be FileRoot, not {:?}", sub_ast));
            }
        }
    }

    Ok(())
}
//
//
pub fn elaborate_axiom(
    program: &mut Program<FolTerm, FolStm>,
    axiom_name: String,
    formula: Expression,
) -> Result<(), String> {
    match Fol::elaborate_expression(formula) {
        Union::R(formula) => {
            program.push_statement(&Axiom(axiom_name, Box::new(formula)));
            Ok(())
        }
        Union::L(term) => {
            type_expected_error(&format!("axiom {}", axiom_name), &term)
        }
    }
}
//
//
pub fn elaborate_let(
    program: &mut Program<FolTerm, FolStm>,
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> Result<(), String> {
    match Fol::elaborate_expression(var_type) {
        Union::R(var_type) => match Fol::elaborate_expression(body) {
            Union::L(body_exp) => {
                program.push_statement(&Let(
                    var_name,
                    Box::new(var_type),
                    Box::new(body_exp),
                ));
                Ok(())
            }

            Union::R(term) => term_expected_error(
                &format!("let definition of {}", var_name),
                &term,
            ),
        },
        Union::L(term) => type_expected_error(
            &format!("let definition of {}", var_name),
            &term,
        ),
    }
}
//
//
pub fn elaborate_fun(
    program: &mut Program<FolTerm, FolStm>,
    fun_name: String,
    args: Vec<(String, Expression)>,
    out_type: Expression,
    body: Expression,
    is_rec: bool,
) -> Result<(), String> {
    match Fol::elaborate_expression(out_type) {
        Union::R(out_type) => match Fol::elaborate_expression(body) {
            Union::L(body) => {
                program.push_statement(&Fun(
                    fun_name,
                    map_typed_variables(&args),
                    Box::new(out_type),
                    Box::new(body),
                    is_rec,
                ));
                Ok(())
            }
            Union::R(type_exp) => term_expected_error(
                &format!("fun definition of {}", fun_name),
                &type_exp,
            ),
        },
        Union::L(term) => type_expected_error(
            &format!("fun definition of {}", fun_name),
            &term,
        ),
    }
}
//
//########################### STATEMENTS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
//TODO include tests for failure on non type expressions i dont
//want to do it now cuz i dont have a real way to distinguish them yet
mod unit_tests {
    use crate::{
        misc::Union,
        parser::api::{Expression, Statement},
        runtime::program::{Program, ProgramNode},
        type_theory::fol::{
            elaboration::{
                elaborate_abstraction, elaborate_application, elaborate_arrow,
                elaborate_forall, elaborate_let, elaborate_var_use,
            },
            fol::{
                Fol,
                FolStm::Let,
                FolTerm::{Abstraction, Application, Variable},
                FolType::{Arrow, Atomic, ForAll},
            },
        },
    };

    #[test]
    fn test_var_elaboration() {
        assert_eq!(
            elaborate_var_use("n".to_string()),
            Union::L(Variable("n".to_string())),
            "Variable elaboration doesnt produce proper term"
        );
        assert_eq!(
            Fol::elaborate_expression(Expression::VarUse("n".to_string())),
            Union::L(Variable("n".to_string())),
            "Top level elaboration doesnt support variables"
        );
        assert_eq!(
            elaborate_var_use("Nat".to_string()),
            Union::R(Atomic("Nat".to_string())),
            "Variable elaboration doesnt produce proper atomic type"
        );
        assert_eq!(
            elaborate_var_use("ListOfNat".to_string()),
            Union::R(Atomic("ListOfNat".to_string())),
            "PascalCase doesnt return a type"
        );
        assert_eq!(
            elaborate_var_use("list_of_nat".to_string()),
            Union::L(Variable("list_of_nat".to_string())),
            "snake_case doesnt return a term"
        );
    }

    #[test]
    fn test_abstraction_elaboration() {
        assert_eq!(
            elaborate_abstraction(
                "x".to_string(),
                Expression::VarUse("Nat".to_string()),
                Expression::VarUse("x".to_string())
            ),
            Ok(Abstraction(
                "x".to_string(),
                Box::new(Atomic("Nat".to_string())),
                Box::new(Variable("x".to_string())),
            )),
            "Abstraction elaboration doesnt produce correct term "
        );
        assert_eq!(
            Fol::elaborate_expression(Expression::Abstraction(
                "x".to_string(),
                Box::new(Expression::VarUse("Nat".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            )),
            Union::L(Abstraction(
                "x".to_string(),
                Box::new(Atomic("Nat".to_string())),
                Box::new(Variable("x".to_string())),
            )),
            "Top level elaboration doesnt support abstraction"
        );
    }

    #[test]
    fn test_application_elaboration() {
        assert_eq!(
            elaborate_application(
                Expression::VarUse("f".to_string()),
                Expression::VarUse("x".to_string())
            ),
            Ok(Application(
                Box::new(Variable("f".to_string())),
                Box::new(Variable("x".to_string())),
            )),
            "Application elaboration doesnt produce correct term"
        );
        assert_eq!(
            Fol::elaborate_expression(Expression::Application(
                Box::new(Expression::VarUse("f".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            )),
            Union::L(Application(
                Box::new(Variable("f".to_string())),
                Box::new(Variable("x".to_string())),
            )),
            "Top level elaboration doesnt support application"
        );
    }

    #[test]
    fn test_arrow_elaboration() {
        assert_eq!(
            elaborate_arrow(
                Expression::VarUse("Nat".to_string()),
                Expression::VarUse("Bool".to_string())
            ),
            Ok(Arrow(
                Box::new(Atomic("Nat".to_string())),
                Box::new(Atomic("Bool".to_string()))
            )),
            "Arrow elaboration doesnt produce proper term"
        );
        assert_eq!(
            Fol::elaborate_expression(Expression::Arrow(
                Box::new(Expression::VarUse("Nat".to_string())),
                Box::new(Expression::VarUse("Bool".to_string())),
            )),
            Union::R(Arrow(
                Box::new(Atomic("Nat".to_string())),
                Box::new(Atomic("Bool".to_string()))
            )),
            "Top level elaboration doesnt support arrow expression"
        );
    }

    #[test]
    fn test_forall_elaboration() {
        assert_eq!(
            elaborate_forall(
                "n".to_string(),
                Expression::VarUse("Nat".to_string()),
                Expression::VarUse("Top".to_string())
            ),
            Ok(ForAll(
                "n".to_string(),
                Box::new(Atomic("Nat".to_string())),
                Box::new(Atomic("Top".to_string()))
            )),
            "For all elaboration doesnt produce proper term"
        );
        assert_eq!(
            Fol::elaborate_expression(Expression::TypeProduct(
                "n".to_string(),
                Box::new(Expression::VarUse("Nat".to_string())),
                Box::new(Expression::VarUse("Top".to_string())),
            )),
            Union::R(ForAll(
                "n".to_string(),
                Box::new(Atomic("Nat".to_string())),
                Box::new(Atomic("Top".to_string()))
            )),
            "Top level elaboration doesnt support forall"
        );
    }

    // TODO support this test too
    // #[test]
    // fn test_fun_elaboration() {}

    #[test]
    fn test_let_elaboration() {
        let mut program = Program::new();
        let res = elaborate_let(
            &mut program,
            "n".to_string(),
            Expression::VarUse("Nat".to_string()),
            Expression::VarUse("zero".to_string()),
        );
        let expected_let = ProgramNode::OfStm(Let(
            "n".to_string(),
            Box::new(Atomic("Nat".to_string())),
            Box::new(Variable("zero".to_string())),
        ));

        assert!(
            res.is_ok(),
            "Let elaboration failed with {}",
            res.err().unwrap()
        );
        assert_eq!(
            program.peek_top_schedule(),
            Some(&expected_let),
            "Let elaboration doesnt push proper term"
        );

        let mut program = Program::new();
        let res = Fol::elaborate_statement(
            Statement::Let(
                "n".to_string(),
                Box::new(Expression::VarUse("Nat".to_string())),
                Box::new(Expression::VarUse("zero".to_string())),
            ),
            &mut program,
        );
        assert!(
            res.is_ok(),
            "Top level let elaboration failed with {}",
            res.err().unwrap()
        );
        assert_eq!(
            program.peek_top_schedule(),
            Some(&expected_let),
            "Top level elaboration doesnt support let"
        );
    }
}

use crate::parser::api::parse_workspace;
use crate::runtime::program::{Program, ProgramNode};
use crate::type_theory::cic::cic::{make_default_environment, CicStm, CicTerm};
use crate::type_theory::interface::TypeTheory;
use crate::{parser::api::NsAst, type_theory::cic::cic::Cic};

pub fn parse_only(workspace: &str) -> Result<NsAst, String> {
    print!("Parsing of workspace: '{}'... ", workspace);
    let ast = parse_workspace(&workspace);
    println!("Done.");

    Ok(ast)
}

//TODO generalize to different type theories
pub fn parse_and_elaborate(
    workspace: &str,
) -> Result<Program<CicTerm, CicStm>, String> {
    let ast = parse_only(workspace)?;
    print!("Elaboration of the AST into a program... ");
    let program = Cic::elaborate_ast(ast);
    println!("Done.");

    Ok(program)
}

//TODO generalize to different type theories
pub fn parse_and_type_check(
    workspace: &str,
) -> Result<Program<CicTerm, CicStm>, String> {
    let program = parse_and_elaborate(workspace)?;
    print!("Type checking of the program... ");
    let environment = &mut make_default_environment();
    let mut errors: Vec<_> = vec![];

    for node in program.schedule_iterable() {
        match node {
            ProgramNode::OfTerm(term) => {
                match Cic::type_check_term(term.clone(), environment) {
                    Err(message) => {
                        errors.push(message);
                    }
                    Ok(_) => {}
                }
            }
            ProgramNode::OfStm(stm) => {
                match Cic::type_check_stm(stm.clone(), environment) {
                    Err(message) => {
                        errors.push(message);
                    }
                    Ok(_) => {}
                }
            }
        }
    }
    println!("Done.");

    if errors.is_empty() {
        Ok(program)
    } else {
        Err(format!(
            "Type checking failed with errors:\n{}",
            errors.join("\n")
        ))
    }
}

//########################### UNIT TESTS
#[test]
fn test_parsing() {
    assert!(
        parse_only("./library").is_ok(),
        "Parsing entrypoint cant process std library"
    );
}

#[test]
fn test_elaboration() {
    assert!(
        parse_and_elaborate("./library").is_ok(),
        "Elaboration entrypoint cant process std library"
    );
}

#[test]
fn test_type_check() {
    let res = parse_and_type_check("./library");
    match res {
        Err(message) => {
            println!("{}", message)
        }
        _ => {}
    }
    assert!(
        parse_and_type_check("./library").is_ok(),
        "Type checking entrypoint cant process std library"
    );
}

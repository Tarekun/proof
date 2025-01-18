use crate::runtime::program::{Program, ProgramNode};
use crate::type_theory::cic::cic::{make_default_environment, CicTerm};
use crate::type_theory::interface::TypeTheory;
use crate::{
    parser::api::{parse_source_file, NsAst},
    type_theory::cic::cic::Cic,
};

pub fn parse_only(workspace: &str) -> Result<NsAst, String> {
    println!("Parsing of file: {}", workspace);
    let (remaining, ast) = parse_source_file(&workspace);
    println!("Parsed AST: {:?}", ast);
    println!("Remaining input: '{}'\n", remaining);

    Ok(ast)
}

//TODO generalize to different type theories
pub fn parse_and_elaborate(
    workspace: &str,
) -> Result<Program<CicTerm>, String> {
    let ast = parse_only(workspace)?;
    println!("Elaboration of the AST into a program");
    let program = Cic::elaborate_ast(ast);

    Ok(program)
}

//TODO generalize to different type theories
pub fn parse_and_type_check(
    workspace: &str,
) -> Result<Program<CicTerm>, String> {
    let program = parse_and_elaborate(workspace)?;
    println!("Type checking of the program");
    let environment = &mut make_default_environment();
    let mut errors = vec![];

    for node in program.schedule_iterable() {
        match node {
            ProgramNode::OfTerm(term) => {
                match Cic::type_check(term.clone(), environment) {
                    Err(message) => {
                        errors.push(message);
                    }
                    _ => {}
                }
            }
            ProgramNode::OfStm(_stm) => {
                //TODO implement statement type checking
            }
        }
    }

    if errors.is_empty() {
        Ok(program)
    } else {
        Err(format!(
            "Type checking failed with errors:\n{}",
            errors.join("\n\n")
        ))
    }
}

//########################### UNIT TESTS
#[test]
fn test_parsing() {}

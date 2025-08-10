use crate::config::Config;
use crate::config::TypeSystem;
use crate::parser::api::LofAst;
use crate::parser::api::LofParser;
use crate::runtime::program::Schedule;
use crate::runtime::program::{Program, ProgramNode};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Reducer, TypeTheory};
use tracing::debug;

#[derive(Debug)]
pub enum EntryPoint {
    Execute,
    TypeCheck,
    Elaborate,
    ParseOnly,
    Help,
}

pub fn parse_only(config: &Config, workspace: &str) -> Result<LofAst, String> {
    debug!("Parsing of workspace: '{}'...", workspace);
    let parser = LofParser::new(config.clone());
    let ast = parser.parse_workspace(config, &workspace)?;
    debug!("Parsing done.");

    Ok(ast)
}

pub fn parse_and_elaborate<T: TypeTheory + Kernel>(
    config: &Config,
    workspace: &str,
) -> Result<Schedule<T>, String> {
    let ast = parse_only(config, workspace)?;
    debug!("Elaboration of the AST into a program...");
    let schedule = T::elaborate_ast(&ast)?;
    debug!("Elaboration done.");
    Ok(schedule)
}

pub fn type_check<T: TypeTheory + Kernel + Reducer>(
    config: &Config,
    workspace: &str,
) -> Result<Program<T>, String> {
    let program: Program<T> = parse_and_elaborate::<T>(config, workspace)?;
    debug!("Type checking of the program...");
    let mut environment: Environment<T::Term, T::Type> =
        T::default_environment();
    let mut errors = vec![];

    for node in program.schedule_iterable() {
        match node {
            ProgramNode::OfTerm(term) => {
                match T::type_check_term(term, &mut environment) {
                    Err(message) => {
                        errors.push(message);
                    }
                    Ok(_) => {}
                }
            }
            ProgramNode::OfStm(stm) => {
                match T::type_check_stm(stm, &mut environment) {
                    Err(message) => {
                        errors.push(message);
                    }
                    Ok(_) => {}
                }
            }
        }
    }
    debug!("Type checking done.");

    if errors.is_empty() {
        Ok(program)
    } else {
        Err(format!(
            "Type checking failed with errors:\n{}",
            errors.join("\n")
        ))
    }
}

pub fn execute<T: TypeTheory + Kernel + Reducer>(
    config: &Config,
    workspace: &str,
) -> Result<(), String> {
    let mut program: Program<T> = type_check(config, workspace)?;
    program.execute()
}

// pub fn interactive<T: TypeTheory + Kernel + Reducer>(
//     // config: &Config,
//     workspace: &str,
// ) -> Result<(), String> {
//     let parser = LofParser::new(Config::new(TypeSystem::Cic()));
//     let mut program = Program::new();

//     while true {
//         let input = "".to_string();
//         if should_exit(input) {
//             break;
//         }

//         let (_, node) = parser.parse_node(input)?;
//         let elaborated_node = qualcosa(node)?;
//         match node {
//             Ex``
//         }
//     }

//     let mut program: Program<T> = type_check(config, workspace)?;
//     program.execute()
// }

pub fn help() {
    println!("Usage: lof <operation> <workspace> [--flags]");
    println!("workspace can be a path to either a .lof file or a directory");
    println!();
    println!("Operations:");
    println!("\trun\t\tExecute the code");
    println!("\tcheck\t\tParse and type check the code");
    println!("\tparse\t\tOnly parse code");
    println!(
        "\telaborate\tParse and map the AST to the configured type system"
    );
    println!();
    println!("Flags:");
    println!("\t--config <path>\t\tSpecify a custom config file path (defaults to ./config.yml)");
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        config::{Config, TypeSystem},
        entrypoints::{execute, parse_and_elaborate, parse_only, type_check},
        type_theory::{cic::cic::Cic, fol::fol::Fol},
    };

    fn all_system_configs() -> Vec<Config> {
        vec![
            Config::default(),
            // Config {
            //     system: TypeSystem::Fol(),
            // },
        ]
    }

    #[test]
    fn test_parsing() {
        for config in all_system_configs() {
            assert!(
                parse_only(&config, "./library").is_ok(),
                "Parsing entrypoint cant process std library"
            );
        }
    }

    #[test]
    fn test_elaboration() {
        for config in all_system_configs() {
            match config.system {
                TypeSystem::Cic() => {
                    assert!(
                        parse_and_elaborate::<Cic>(&config, "./library")
                            .is_ok(),
                        "Elaboration entrypoint cant process std library"
                    );
                }
                TypeSystem::Fol() => {
                    assert!(
                        parse_and_elaborate::<Fol>(&config, "./library")
                            .is_ok(),
                        "Elaboration entrypoint cant process std library"
                    );
                }
            }
        }
    }

    //TODO test everything
    #[test]
    fn test_type_check() {
        for config in all_system_configs() {
            let res = type_check::<Cic>(&config, "./library");
            assert!(
                type_check::<Cic>(&config, "./library").is_ok(),
                "Type checking entrypoint cant process std library:\n{:?}",
                res.err()
            );
        }
    }

    #[test]
    fn test_execution() {
        for config in all_system_configs() {
            let res = match config.system {
                TypeSystem::Cic() => execute::<Cic>(&config, "./library"),
                TypeSystem::Fol() => execute::<Fol>(&config, "./library"),
            };
            assert!(
                res.is_ok(),
                "Execution cant process std library:\n{:?}",
                res.err()
            );
        }
    }
}

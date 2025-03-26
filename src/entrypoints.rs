use crate::config::Config;
use crate::parser::api::LofParser;
use crate::parser::api::NsAst;
use crate::runtime::program::{Program, ProgramNode};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

pub fn parse_only(config: &Config, workspace: &str) -> Result<NsAst, String> {
    print!("Parsing of workspace: '{}'... ", workspace);
    let parser = LofParser::new(config.clone());
    let ast = parser.parse_workspace(config, &workspace)?;
    println!("Done.");

    Ok(ast)
}

pub fn parse_and_elaborate<T: TypeTheory>(
    config: &Config,
    workspace: &str,
) -> Result<Program<T::Term, T::Stm>, String> {
    let ast = parse_only(config, workspace)?;
    print!("Elaboration of the AST into a program... ");
    let program = T::elaborate_ast(ast);
    println!("Done.");
    Ok(program)
}

pub fn parse_and_type_check<T: TypeTheory>(
    config: &Config,
    workspace: &str,
) -> Result<Program<T::Term, T::Stm>, String> {
    let program: Program<T::Term, T::Stm> =
        parse_and_elaborate::<T>(config, workspace)?;
    print!("Type checking of the program... ");
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
#[cfg(test)]
mod unit_tests {
    use crate::{
        config::{Config, TypeSystem},
        entrypoints::{parse_and_elaborate, parse_and_type_check, parse_only},
        type_theory::{cic::cic::Cic, fol::fol::Fol},
    };

    fn all_system_configs() -> Vec<Config> {
        vec![
            Config {
                system: TypeSystem::Cic(),
            },
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
            let res = parse_and_type_check::<Cic>(&config, "./library");
            match res {
                Err(message) => {
                    println!("{}", message)
                }
                _ => {}
            }
            let res = parse_and_type_check::<Cic>(&config, "./library");
            assert!(
                parse_and_type_check::<Cic>(&config, "./library").is_ok(),
                "Type checking entrypoint cant process std library:\n{:?}",
                res.err()
            );
        }
    }
}

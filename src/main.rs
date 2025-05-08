mod cli;
mod config;
mod entrypoints;
mod file_manager;
mod logger;
mod misc;
mod parser {
    pub mod api;
    mod commons;
    mod expressions;
    mod statements;
    mod tactics;
}
mod runtime {
    pub mod program;
}
mod type_theory {
    // pub mod commons;
    pub mod environment;
    pub mod interface;
    pub mod commons {
        pub mod evaluation;
        pub mod type_check;
        pub mod utils;
    }
    pub mod cic {
        pub mod cic;
        pub mod cic_utils;
        pub mod elaboration;
        pub mod evaluation;
        pub mod type_check;
        pub mod unification;
    }
    // pub mod stlc {
    //     pub mod elaboration;
    //     pub mod stlc;
    // }
    pub mod fol {
        pub mod elaboration;
        pub mod evaluation;
        pub mod fol;
        pub mod fol_utils;
        pub mod type_check;
    }
}

use cli::get_flag_value;
use config::{load_config, Config, TypeSystem};
use entrypoints::{
    execute, help, parse_and_elaborate, parse_only, type_check, EntryPoint,
};
use logger::init_logger;
use std::env;
use tracing::{debug, error, info};
use type_theory::{cic::cic::Cic, fol::fol::Fol, interface::TypeTheory};

fn determine_entrypoint(args: &[String]) -> EntryPoint {
    if args.contains(&"--typecheck".to_string())
        || args.contains(&"-t".to_string())
    {
        EntryPoint::TypeCheck
    } else if args.contains(&"--elaborate".to_string())
        || args.contains(&"-e".to_string())
    {
        EntryPoint::Elaborate
    } else if args.contains(&"--parse".to_string())
        || args.contains(&"-p".to_string())
    {
        EntryPoint::ParseOnly
    } else if args.contains(&"--help".to_string())
        || args.contains(&"-h".to_string())
    {
        EntryPoint::Help
    } else {
        EntryPoint::Execute
    }
}

fn run_with_theory<T: TypeTheory>(
    config: Config,
    filepath: &str,
    entrypoint: EntryPoint,
) {
    match entrypoint {
        EntryPoint::Execute => match execute::<T>(&config, filepath) {
            Ok(_) => {}
            Err(message) => error!("Program failed: {}", message),
        },
        EntryPoint::TypeCheck => match type_check::<T>(&config, filepath) {
            Ok(program) => {
                for node in program.schedule_iterable() {
                    debug!("node in the type checked program: {:?}", node);
                }
            }
            Err(message) => error!("Program failed: {}", message),
        },
        EntryPoint::Elaborate => {
            match parse_and_elaborate::<T>(&config, filepath) {
                Ok(program) => {
                    for node in program.schedule_iterable() {
                        debug!("node in the elaborated program: {:?}", node);
                    }
                }
                Err(message) => error!("Program failed: {}", message),
            }
        }
        EntryPoint::ParseOnly => match parse_only(&config, filepath) {
            Ok(ast) => info!("Parsed AST: {:?}", ast),
            Err(message) => error!("Program failed: {}", message),
        },
        EntryPoint::Help => help(),
    }
}

fn main() {
    println!("################ PROGRAM START #################\n");

    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        println!("Usage: cargo run <workspace> [--flags]");
        return;
    }

    let filepath = &args[1];

    let config_path = match get_flag_value(&args, "--config") {
        Some(path) => path,
        None => "./config.yml".to_string(),
    };
    let config: config::Config = load_config(&config_path).unwrap();
    init_logger(&config);
    info!("Specified config: {:?}", config);

    let entrypoint = determine_entrypoint(&args);
    info!("Requested entrypoint: {:?}", entrypoint);

    match config.system {
        TypeSystem::Cic() => {
            run_with_theory::<Cic>(config, &filepath, entrypoint)
        }
        TypeSystem::Fol() => {
            run_with_theory::<Fol>(config, &filepath, entrypoint)
        }
    };
}

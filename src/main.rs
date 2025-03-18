mod cli;
mod config;
mod entrypoints;
mod file_manager;
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
    pub mod cic {
        pub mod cic;
        pub mod cic_utils;
        pub mod elaboration;
        // pub mod evaluation;
        pub mod type_check;
        pub mod unification;
    }
    // pub mod stlc {
    //     pub mod elaboration;
    //     pub mod stlc;
    // }
    pub mod fol {
        pub mod elaboration;
        pub mod fol;
        pub mod type_check;
    }
}

use cli::get_flag_value;
use config::{load_config, Config, TypeSystem};
use entrypoints::parse_and_type_check;
use std::env;
use type_theory::{cic::cic::Cic, fol::fol::Fol, interface::TypeTheory};

fn run_with_theory<T: TypeTheory>(config: Config, filepath: &str) {
    match parse_and_type_check::<T>(&config, filepath) {
        Ok(program) => {
            for node in program.schedule_iterable() {
                println!("node in the scheduled program: {:?}\n", node);
            }
        }
        Err(message) => println!("Program failed: {}", message),
    }
}

fn main() {
    println!("################ PROGRAM START #################\n");

    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: cargo run <filepath.ns>");
        return;
    }

    let filepath = &args[1];

    let config_path = match get_flag_value(&args, "--config") {
        Some(path) => path,
        None => "./config.yml".to_string(),
    };
    let config: config::Config = load_config(&config_path).unwrap();
    println!("Specified config: {:?}", config);

    match config.system {
        TypeSystem::Cic() => run_with_theory::<Cic>(config, &filepath),
        TypeSystem::Fol() => run_with_theory::<Fol>(config, &filepath),
    };
}

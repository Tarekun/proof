mod entrypoints;
mod file_manager;
mod parser {
    pub mod api;
    mod commons;
    mod expressions;
    mod statements;
}
mod runtime {
    pub mod program;
}
mod type_theory {
    pub mod environment;
    pub mod interface;
    pub mod cic {
        pub mod cic;
        pub mod elaboration;
        pub mod evaluation;
        pub mod type_check;
    }
    pub mod stlc {
        pub mod elaboration;
        pub mod stlc;
    }
}

use entrypoints::parse_and_type_check;
use std::env;

fn main() {
    println!("################ PROGRAM START #################\n");

    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: cargo run <filepath.ns>");
        return;
    }

    let filepath = &args[1];

    match parse_and_type_check(&filepath) {
        Ok(program) => {
            for node in program.schedule_iterable() {
                println!("Program failed: {:?}", node);
            }
        }
        Err(message) => {
            println!("Program failed: {}", message);
        }
    }
}

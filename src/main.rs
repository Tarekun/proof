mod file_manager;
mod parsing;
mod type_theory {
    pub mod cic {
        pub mod cic;
        pub mod elaboration;
        mod tests;
        pub mod type_check;
    }
    pub mod environment;
    pub mod interface;
    // pub mod stlc {
    //     pub mod elaboration;
    //     pub mod stlc;
    //     mod tests;
    // }
}

use crate::type_theory::interface::TypeTheory;
use std::env;
use type_theory::cic::cic::Cic;

fn main() {
    println!("################ PROGRAM START #################\n");

    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: cargo run <filepath.ns>");
        return;
    }

    let filepath = &args[1];
    let (remaining, ast) = parsing::parse_source_file(&filepath);
    println!("Parsed AST: {:?}", ast);
    println!("Remaining input: '{}'\n", remaining);

    // let environment = Stlc::elaborate_ast(ast);
    let environment = Cic::elaborate_ast(ast);
    for definition in environment.deltas {
        let (var_name, term) = definition;
        println!("defined term {:?}: {:?}", var_name, term);
    }

    println!("\nContext:");
    for assumption in environment.context {
        let (var_name, var_type) = assumption;
        println!("var {:?} : {:?}", var_name, var_type);
    }
}

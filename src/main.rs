use std::env;

mod file_manager;
mod parsing;
mod type_theory {
    pub mod environment;
    pub mod stlc;
}

fn main() {
    println!("################ PROGRAM START #################\n");

    // Get the file path from command line arguments
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: cargo run <filepath.ns>");
        return;
    }

    let filepath = &args[1];
    let (remaining, ast) = parsing::parse_source_file(&filepath);
    println!("Parsed AST: {:?}", ast);
    println!("Remaining input: '{}'\n", remaining);

    let environment = type_theory::stlc::evaluate_ast(ast);
    for definition in environment.deltas {
        let (var_name, term) = definition;
        println!("defined term {:?}: {:?}", var_name, term);
    }
}

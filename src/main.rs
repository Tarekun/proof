mod cic;
mod parsing;

fn main() {
    println!("################ INIZIO PROGRAMMA #################\n");

    let input = r"let f = (λx. x x)   ;";
    match parsing::parse_lambda_calculus(input) {
        Ok((remaining, ast)) => {
            println!("Parsed AST: {:?}", ast);
            println!("Remaining input: '{}'\n", remaining);

            let terms = cic::evaluate_ast(ast);
            println!("Mapped terms: {:?}", terms);
        }
        Err(e) => println!("Error: {:?}", e),
    }
}

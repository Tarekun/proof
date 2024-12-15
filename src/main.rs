mod parsing;

fn main() {
    println!("################ INIZIO PROGRAMMA #################\n");

    let input = r"x z y";
    match parsing::parse_lambda_calculus(input) {
        Ok((remaining, ast)) => {
            println!("Parsed AST: {:?}", ast);
            println!("Remaining input: '{}'", remaining);
        }
        Err(e) => println!("Error: {:?}", e),
    }
}

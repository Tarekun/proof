use nom::{
    branch::alt,
    character::complete::{alpha1, alphanumeric0, char, multispace0, multispace1, one_of},
    combinator::{map, recognize},
    multi::many0,
    sequence::{delimited, pair, preceded, tuple},
    IResult,
};

#[derive(Debug, PartialEq)]
pub enum StlcTerm {
    Var(String),
    Abs(String, Box<StlcTerm>),
    App(Box<StlcTerm>, Box<StlcTerm>),
}

// Parser to match and discard whitespace (space, newline, tab, carriage return)
fn parse_whitespace(input: &str) -> IResult<&str, &str> {
    map(many0(one_of(" \n\r\t")), |_| "")(input)
}
// Parser for a term wrapped in parentheses
fn parse_parens(input: &str) -> IResult<&str, StlcTerm> {
    delimited(
        preceded(multispace0, char('(')), // Match '(' with leading whitespace
        parse_term,                       // Parse the inner term
        preceded(multispace0, char(')')), // Match ')' with trailing whitespace
    )(input)
}
// Parser for a generic identifier (starts with a letter, followed by letters, digits, or underscores)
fn parse_identifier(input: &str) -> IResult<&str, &str> {
    recognize(pair(alpha1, alphanumeric0))(input)
}

// Parser for a variable
fn parse_var(input: &str) -> IResult<&str, StlcTerm> {
    map(parse_identifier, |s: &str| StlcTerm::Var(s.to_string()))(input)
}

// Parser for a lambda abstraction
fn parse_abs(input: &str) -> IResult<&str, StlcTerm> {
    let (input, _) = preceded(multispace0, alt((char('λ'), char('\\'))))(input)?;
    let (input, var_name) = preceded(multispace0, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, char('.'))(input)?;
    let (input, body) = preceded(multispace0, parse_term)(input)?;

    Ok((input, StlcTerm::Abs(var_name.to_string(), Box::new(body))))
}

// Parser for function application
fn parse_app(input: &str) -> IResult<&str, StlcTerm> {
    let (input, left) = preceded(multispace0, parse_atom)(input)?; // Parse the left term (atomic term)
    let (input, _) = multispace1(input)?; // Ensure at least one space between terms
    let (input, right) = preceded(multispace0, parse_term)(input)?; // Parse the right term

    Ok((input, StlcTerm::App(Box::new(left), Box::new(right))))
}

// Atomic term parser used for function application
fn parse_atom(input: &str) -> IResult<&str, StlcTerm> {
    alt((parse_parens, parse_abs, parse_var))(input) // Atomic terms are parenthesized terms, abstractions, or variables
}
// Main term parser that decides between variables, abstractions, or applications
fn parse_term(input: &str) -> IResult<&str, StlcTerm> {
    alt((parse_app, parse_parens, parse_var, parse_abs))(input)
}

// Utility to parse and get the full result
pub fn parse_lambda_calculus(input: &str) -> IResult<&str, StlcTerm> {
    let (input, result) = parse_term(input)?;
    Ok((input, result))
}

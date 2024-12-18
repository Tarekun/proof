use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{
        alpha1, alphanumeric0, char, digit1, multispace0, multispace1,
    },
    combinator::{map, map_res, recognize},
    error::{Error, ErrorKind},
    multi::many0,
    sequence::{delimited, pair, preceded, terminated},
    IResult,
};

use crate::file_manager;

#[derive(Debug, PartialEq)]
pub enum NsAst {
    Var(String),
    Abs(String, Box<NsAst>),
    App(Box<NsAst>, Box<NsAst>),
    Num(i64),
    Let(String, Box<NsAst>),
    FileRoot(String, Vec<NsAst>),
}
const RESERVED_KEYWORDS: [&str; 1] = ["let"];

fn parse_parens(input: &str) -> IResult<&str, NsAst> {
    delimited(
        preceded(multispace0, char('(')), // Match '(' with leading whitespace
        parse_term,                       // Parse the inner term
        preceded(multispace0, char(')')), // Match ')' with trailing whitespace
    )(input)
}
fn parse_identifier(input: &str) -> IResult<&str, &str> {
    let (input, identifier) = recognize(pair(alpha1, alphanumeric0))(input)?;

    if RESERVED_KEYWORDS.contains(&identifier) {
        Err(nom::Err::Error(Error::new(input, ErrorKind::Tag))) // Reject reserved keywords
    } else {
        Ok((input, identifier)) // Successfully parsed a valid identifier
    }
}
fn parse_numeral(input: &str) -> IResult<&str, NsAst> {
    map_res(
        preceded(multispace0, digit1), // Pass `digit1` as a parser, do not call it.
        |s: &str| s.parse::<i64>().map(NsAst::Num), // Convert to `i64` and wrap in `NsAst::Num`.
    )(input)
}

fn parse_var(input: &str) -> IResult<&str, NsAst> {
    map(parse_identifier, |s: &str| NsAst::Var(s.to_string()))(input)
}

fn parse_abs(input: &str) -> IResult<&str, NsAst> {
    let (input, _) =
        preceded(multispace0, alt((char('λ'), char('\\'))))(input)?;
    let (input, var_name) = preceded(multispace0, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, char('.'))(input)?;
    let (input, body) = preceded(multispace0, parse_term)(input)?;

    Ok((input, NsAst::Abs(var_name.to_string(), Box::new(body))))
}

fn parse_app(input: &str) -> IResult<&str, NsAst> {
    let (input, left) = preceded(multispace0, parse_atom)(input)?; // Parse the left term (atomic term)
    let (input, _) = multispace1(input)?; // Ensure at least one space between terms
    let (input, right) = preceded(multispace0, parse_term)(input)?; // Parse the right term

    Ok((input, NsAst::App(Box::new(left), Box::new(right))))
}

fn parse_let(input: &str) -> IResult<&str, NsAst> {
    let (input, _) = preceded(multispace0, tag("let"))(input)?;
    let (input, var_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, char('='))(input)?;
    let (input, term) = preceded(multispace0, parse_term)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    Ok((input, NsAst::Let(var_name.to_string(), Box::new(term))))
}

//TODO: refactor these 2, this is ridiculous
fn atomic_parsers<'a>() -> impl FnMut(&'a str) -> IResult<&'a str, NsAst> {
    alt((parse_parens, parse_abs, parse_var, parse_numeral))
}
// Atomic term parser used for function application
fn parse_atom(input: &str) -> IResult<&str, NsAst> {
    atomic_parsers()(input)
}
// Main term parser that decides between variables, abstractions, or applications
fn parse_term(input: &str) -> IResult<&str, NsAst> {
    alt((parse_app, parse_let, atomic_parsers()))(input)
}

pub fn parse_source_file(filepath: &str) -> (String, NsAst) {
    let source = match file_manager::read_file(filepath) {
        Ok(content) => content,
        Err(e) => {
            panic!("Error reading file: {:?}", e);
        }
    };
    let result = many0(parse_term)(&source);
    let (remaining_input, terms) = match result {
        Ok((remaining, terms)) => (remaining, terms),
        Err(e) => {
            panic!("Parsing error: {:?}", e);
        }
    };

    (
        remaining_input.to_string(),
        NsAst::FileRoot(filepath.to_string(), terms),
    )
}

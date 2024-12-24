use crate::file_manager;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{
        alpha1, alphanumeric0, char, digit1, line_ending, multispace0,
        multispace1, not_line_ending,
    },
    combinator::{map, map_res, opt, recognize},
    error::{Error, ErrorKind},
    multi::many0,
    sequence::{delimited, pair, preceded},
    IResult,
};

#[derive(Debug, PartialEq)]
pub enum Statement {
    Comment(),
    FileRoot(String, Vec<NsAst>),
    Let(String, Box<Expression>),
    Axiom(String, Box<Expression>),
}
#[derive(Debug, PartialEq)]
pub enum Expression {
    VarUse(String),
    /// (var_name, var_type, function_body)
    Abstraction(String, Box<Expression>, Box<Expression>),
    /// (var_name, var_type, dependent_type)
    TypeProduct(String, Box<Expression>, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
    Num(i64),
}
#[derive(Debug, PartialEq)]
pub enum NsAst {
    Stm(Statement),
    Exp(Expression),
}

const RESERVED_KEYWORDS: [&str; 2] = ["let", "axiom"];
fn generic_err(input: &str) -> IResult<&str, NsAst> {
    //TODO ever support an error message?
    Err(nom::Err::Error(Error::new(input, ErrorKind::Tag)))
}

//########################### BASIC TOKEN PARSERS
fn parse_parens(input: &str) -> IResult<&str, NsAst> {
    delimited(
        preceded(multispace0, char('(')),
        parse_term,
        preceded(multispace0, char(')')),
    )(input)
}
fn parse_identifier(input: &str) -> IResult<&str, &str> {
    let (input, identifier) =
        preceded(multispace0, recognize(pair(alpha1, alphanumeric0)))(input)?;

    if RESERVED_KEYWORDS.contains(&identifier) {
        Err(nom::Err::Error(Error::new(input, ErrorKind::Tag)))
    } else {
        Ok((input, identifier))
    }
}
fn parse_numeral(input: &str) -> IResult<&str, NsAst> {
    map_res(preceded(multispace0, digit1), |s: &str| {
        s.parse::<i64>()
            .map(|num: i64| NsAst::Exp(Expression::Num(num)))
    })(input)
}
fn parse_comment(input: &str) -> IResult<&str, NsAst> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("#")(input)?;
    let (input, _) = not_line_ending(input)?;
    let (input, _) = opt(line_ending)(input)?;

    Ok((input, NsAst::Stm(Statement::Comment())))
}
//########################### BASIC TOKEN PARSERS

//########################### EXPRESSION PARSERS
fn parse_var(input: &str) -> IResult<&str, NsAst> {
    map(parse_identifier, |s: &str| {
        NsAst::Exp(Expression::VarUse(s.to_string()))
    })(input)
}

fn parse_abs(input: &str) -> IResult<&str, NsAst> {
    let (input, _) =
        preceded(multispace0, alt((tag("λ"), tag("\\lambda "))))(input)?;
    let (input, var_name) = preceded(multispace0, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, type_var) = preceded(multispace0, parse_var)(input)?;
    let (input, _) = preceded(multispace0, char('.'))(input)?;
    let (input, body) = preceded(multispace0, parse_term)(input)?;

    match body {
        NsAst::Exp(body_exp) => match type_var {
            NsAst::Exp(type_exp) => Ok((
                input,
                NsAst::Exp(Expression::Abstraction(
                    var_name.to_string(),
                    Box::new(type_exp),
                    Box::new(body_exp),
                )),
            )),
            NsAst::Stm(_) => generic_err(input),
        },
        NsAst::Stm(_) => generic_err(input),
    }
}

fn parse_type_abs(input: &str) -> IResult<&str, NsAst> {
    let (input, _) =
        preceded(multispace0, alt((tag("Π"), tag("\\forall"))))(input)?;
    let (input, var_name) = preceded(multispace0, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, type_var) = preceded(multispace0, parse_var)(input)?;
    let (input, _) = preceded(multispace0, char('.'))(input)?;
    let (input, body) = preceded(multispace0, parse_term)(input)?;

    match body {
        NsAst::Exp(body_exp) => match type_var {
            NsAst::Exp(type_exp) => Ok((
                input,
                NsAst::Exp(Expression::TypeProduct(
                    var_name.to_string(),
                    Box::new(type_exp),
                    Box::new(body_exp),
                )),
            )),
            NsAst::Stm(_) => generic_err(input),
        },
        NsAst::Stm(_) => generic_err(input),
    }
}

fn parse_app(input: &str) -> IResult<&str, NsAst> {
    let (input, left) = preceded(multispace0, parse_atom)(input)?; // Parse the left term (atomic term)
    let (input, _) = multispace1(input)?;
    let (input, right) = preceded(multispace0, parse_term)(input)?;

    match left {
        NsAst::Exp(left_exp) => match right {
            NsAst::Exp(right_exp) => Ok((
                input,
                NsAst::Exp(Expression::Application(
                    Box::new(left_exp),
                    Box::new(right_exp),
                )),
            )),
            NsAst::Stm(_) => generic_err(input),
        },
        NsAst::Stm(_) => generic_err(input),
    }
}

fn parse_let(input: &str) -> IResult<&str, NsAst> {
    let (input, _) = preceded(multispace0, tag("let"))(input)?;
    let (input, var_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":="))(input)?;
    let (input, term) = preceded(multispace0, parse_term)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    match term {
        NsAst::Exp(exp) => Ok((
            input,
            NsAst::Stm(Statement::Let(var_name.to_string(), Box::new(exp))),
        )),
        NsAst::Stm(_) => generic_err(input),
    }
}
//########################### EXPRESSION PARSERS

//########################### STATEMENT PARSERS
fn parse_axiom(input: &str) -> IResult<&str, NsAst> {
    let (input, _) = preceded(multispace0, tag("axiom"))(input)?;
    let (input, axiom_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, term) = preceded(multispace0, parse_term)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    match term {
        NsAst::Exp(exp) => Ok((
            input,
            NsAst::Stm(Statement::Axiom(axiom_name.to_string(), Box::new(exp))),
        )),
        NsAst::Stm(_) => generic_err(input),
    }
}
//########################### STATEMENT PARSERS

//TODO: refactor these 2, this is ridiculous
fn atomic_parsers<'a>() -> impl FnMut(&'a str) -> IResult<&'a str, NsAst> {
    alt((
        parse_parens,
        parse_abs,
        parse_type_abs,
        parse_var,
        parse_numeral,
        parse_comment,
        parse_axiom,
    ))
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
        NsAst::Stm(Statement::FileRoot(filepath.to_string(), terms)),
    )
}

#[test]
fn test_tokens_parser() {
    // identifier tests
    assert!(
        parse_identifier("test").is_ok(),
        "Parser cant read identifiers"
    );
    assert_eq!(
        parse_identifier("  test").unwrap(),
        ("", "test"),
        "Identifier parser cant cope with whitespaces"
    );
    assert!(
        parse_identifier("test123").is_ok(),
        "Identifier parser cant read numbers/underscores"
    );

    // comment tests
    assert!(parse_comment("#abc\n").is_ok(), "Parser cant read comments");
    assert!(
        parse_comment("#abc").is_ok(),
        "Parser cant read comments at end of input"
    );

    // parenthesis tests
    assert!(
        parse_parens("(x)").is_ok(),
        "Parser cant cope with parenthesis"
    );
    assert!(
        parse_parens("((x))").is_ok(),
        "Parser cant cope with nested parenthesis"
    );
    assert!(
        parse_parens("(x").is_err(),
        "Parser accepts unmatched parenthesis"
    );
    assert!(
        parse_parens("x)").is_err(),
        "Parser accepts unmatched parenthesis"
    );
}

#[test]
fn test_axiom() {
    assert!(
        parse_axiom("axiom nat:TYPE;").is_ok(),
        "Identifier cant read axioms"
    );
    assert!(
        parse_axiom("axiom  nat :\tTYPE  ;").is_ok(),
        "Axiom parser cant cope with multispaces"
    );
    assert!(
        parse_axiom("axiomnat:TYPE;").is_err(),
        "Axiom parser doesnt split 'axiom' keyword and axiom identifier"
    );
    assert!(
        parse_term("axiom nat:TYPE;").is_ok(),
        "Top level parser can't read axioms"
    );
}

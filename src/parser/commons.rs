use super::{
    api::Expression,
    expressions::{
        parse_app, parse_arrow_type, parse_parens, parse_type_abs, parse_var,
    },
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{
        alpha1, alphanumeric0, char, digit1, multispace0, multispace1,
    },
    combinator::{map_res, recognize},
    error::{Error, ErrorKind},
    multi::many0,
    sequence::{delimited, pair, preceded},
    IResult,
};

const RESERVED_KEYWORDS: [&str; 11] = [
    "let",
    "axiom",
    "inductive",
    "match",
    "with",
    "theorem",
    "lemma",
    "proposition",
    "qed",
    "fun",
    "rec",
];

//########################### BASIC TOKEN PARSERS
pub fn parse_identifier(input: &str) -> IResult<&str, &str> {
    let (input, identifier) =
        preceded(multispace0, recognize(pair(alpha1, alphanumeric0)))(input)?;

    if RESERVED_KEYWORDS.contains(&identifier) {
        Err(nom::Err::Error(Error::new(input, ErrorKind::Tag)))
    } else {
        Ok((input, identifier))
    }
}
pub fn parse_numeral(input: &str) -> IResult<&str, Expression> {
    map_res(preceded(multispace0, digit1), |s: &str| {
        s.parse::<i64>().map(|num: i64| Expression::Num(num))
    })(input)
}
//########################### BASIC TOKEN PARSERS

pub fn parse_type_expression(input: &str) -> IResult<&str, Expression> {
    alt((
        parse_arrow_type,
        parse_parens,
        // application should show up before parse_var
        // otherwise the function will be parsed as normal variable
        // and the rest of the string is not properly parsed
        parse_app,
        parse_var,
        parse_type_abs,
    ))(input)
}

pub fn parse_typed_identifier(
    input: &str,
) -> IResult<&str, (String, Expression)> {
    let (input, identifier) = preceded(multispace0, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, type_expression) =
        preceded(multispace0, parse_type_expression)(input)?;

    Ok((input, (identifier.to_string(), type_expression)))
}
pub fn typed_parameter_list(
    input: &str,
) -> IResult<&str, Vec<(String, Expression)>> {
    many0(preceded(
        multispace1,
        delimited(
            preceded(multispace0, char('(')),
            parse_typed_identifier,
            preceded(multispace0, char(')')),
        ),
    ))(input)
}

//########################### UNIT TESTS
#[test]
fn test_identifier() {
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
}

#[test]
fn test_type_expression() {
    assert_eq!(
        parse_type_expression("TYPE").unwrap(),
        ("", (Expression::VarUse("TYPE".to_string()))),
        "parse_type_expression cant read simple sorts"
    );
    assert!(
        parse_type_expression("A -> B").is_ok(),
        "parse_type_expression cant read arrow types"
    );
    assert!(
        parse_type_expression("(ΠT:TYPE.T)").is_ok(),
        "parse_type_expression cant read types enclosed in parethesis"
    );
}

#[test]
fn test_typed_identifier() {
    assert_eq!(
        parse_typed_identifier("x : TYPE").unwrap(),
        (
            "",
            ("x".to_string(), Expression::VarUse("TYPE".to_string()))
        ),
        "parse_typed_identifier doesnt return as expected"
    );
    assert_eq!(
        parse_typed_identifier("\r\tx \t  : \t  TYPE").unwrap(),
        (
            "",
            ("x".to_string(), Expression::VarUse("TYPE".to_string()))
        ),
        "parse_typed_identifier cant cope with whitespaces"
    );
    assert!(
        parse_typed_identifier("x:TYPE").is_ok(),
        "parse_typed_identifier cant cope with dense notation"
    );
}

use super::api::{Expression, LofParser};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{
        alpha1, alphanumeric0, char, multispace0, multispace1,
    },
    combinator::{opt, recognize},
    error::{Error, ErrorKind},
    multi::many0,
    sequence::{delimited, pair, preceded},
    IResult,
};

const RESERVED_KEYWORDS: [&str; 12] = [
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
    "import",
];

impl LofParser {
    pub fn parse_identifier<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, &'a str> {
        let (input, identifier) = preceded(
            multispace0,
            recognize(pair(alpha1, alphanumeric0)),
        )(input)?;

        if RESERVED_KEYWORDS.contains(&identifier) {
            Err(nom::Err::Error(Error::new(input, ErrorKind::Tag)))
        } else {
            Ok((input, identifier))
        }
    }

    pub fn parse_type_expression<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        alt((
            |input| self.parse_arrow_type(input),
            |input| self.parse_parens(input),
            // application should show up before parse_var
            // otherwise the function will be parsed as normal variable
            // and the rest of the string is not properly parsed
            |input| self.parse_app(input),
            |input| self.parse_var(input),
            |input| self.parse_type_abs(input),
        ))(input)
    }

    pub fn parse_typed_identifier<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, (String, Expression)> {
        let (input, identifier) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        let (input, type_expression) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;

        Ok((input, (identifier.to_string(), type_expression)))
    }

    pub fn parse_optionally_typed_identifier<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, (String, Option<Expression>)> {
        let (input, identifier) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;
        let (input, opt_type) = opt(preceded(
            multispace0,
            preceded(
                tag(":"),
                preceded(multispace0, |input| {
                    self.parse_type_expression(input)
                }),
            ),
        ))(input)?;

        Ok((input, (identifier.to_string(), opt_type)))
    }

    pub fn typed_parameter_list<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Vec<(String, Expression)>> {
        many0(preceded(
            multispace1,
            delimited(
                preceded(multispace0, char('(')),
                |input| self.parse_typed_identifier(input),
                preceded(multispace0, char(')')),
            ),
        ))(input)
    }
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        config::Config,
        parser::api::{Expression, LofParser},
    };

    #[test]
    fn test_identifier() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_identifier("test").is_ok(),
            "Parser cant read identifiers"
        );
        assert_eq!(
            parser.parse_identifier("  test").unwrap(),
            ("", "test"),
            "Identifier parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_identifier("test123").is_ok(),
            "Identifier parser cant read numbers/underscores"
        );
    }

    #[test]
    fn test_type_expression() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_type_expression("TYPE").unwrap(),
            ("", (Expression::VarUse("TYPE".to_string()))),
            "parse_type_expression cant read simple sorts"
        );
        assert!(
            parser.parse_type_expression("A -> B").is_ok(),
            "parse_type_expression cant read arrow types"
        );
        assert!(
            parser.parse_type_expression("(ΠT:TYPE.T)").is_ok(),
            "parse_type_expression cant read types enclosed in parethesis"
        );
    }

    #[test]
    fn test_typed_identifier() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_typed_identifier("x : TYPE").unwrap(),
            (
                "",
                ("x".to_string(), Expression::VarUse("TYPE".to_string()))
            ),
            "parse_typed_identifier doesnt return as expected"
        );
        assert_eq!(
            parser
                .parse_typed_identifier("\r\tx \t  : \t  TYPE")
                .unwrap(),
            (
                "",
                ("x".to_string(), Expression::VarUse("TYPE".to_string()))
            ),
            "parse_typed_identifier cant cope with whitespaces"
        );
        assert!(
            parser.parse_typed_identifier("x:TYPE").is_ok(),
            "parse_typed_identifier cant cope with dense notation"
        );
    }
}

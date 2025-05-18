use nom::branch::alt;
use nom::character::complete::multispace1;
use nom::error::{Error, ErrorKind};
use nom::multi::many0;
use nom::{
    bytes::complete::tag, character::complete::multispace0, sequence::preceded,
    IResult,
};

use super::api::Tactic::{Begin, Qed, Suppose};
use super::api::{Expression, LofParser, Tactic};

//########################### TACTICS PARSER
impl LofParser {
    fn begin<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("begin"))(input)?;
        Ok((input, Begin()))
    }

    fn qed<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("qed."))(input)?;
        Ok((input, Qed()))
    }

    fn suppose<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Tactic<Expression>> {
        let (input, _) = preceded(multispace0, tag("suppose"))(input)?;
        let (input, (var_name, opt_type)) = preceded(multispace1, |input| {
            self.parse_optionally_typed_identifier(input)
        })(input)?;

        Ok((
            input,
            Suppose(
                var_name.to_string(),
                opt_type.unwrap_or(Expression::Inferator()),
            ),
        ))
    }

    pub fn parse_tactic<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Tactic<Expression>> {
        alt((
            |input| self.begin(input),
            |input| self.qed(input),
            |input| self.suppose(input),
        ))(input)
    }

    pub fn parse_interactive_proof<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Vec<Tactic<Expression>>> {
        let (input, partial_proof) =
            many0(|input| self.parse_tactic(input))(input)?;

        if partial_proof.len() > 0 && partial_proof[0] != Begin() {
            // TODO return a better error here
            // return Err("Interactive proofs must start with a 'begin' tactic");
            let error = nom::Err::Error(Error::new(input, ErrorKind::Tag));
            return Err(error);
        }
        Ok((input, partial_proof))
    }
}
//########################### TACTICS PARSER

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        config::Config,
        parser::api::Expression::VarUse,
        parser::api::LofParser,
        parser::api::Tactic::{Begin, Qed, Suppose},
    };

    #[test]
    fn test_interactive_proof() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_interactive_proof("begin qed."),
            Ok(("", vec![Begin(), Qed()])),
            "Interactive proof parser doesnt construct proper AST"
        );
        assert!(
            parser.parse_interactive_proof("begin").is_ok(),
            "Interactive proof parser doesnt read partial proof"
        );
        assert!(
            parser.parse_interactive_proof("suppose n:Nat").is_err(), 
            "Interactive proof parser reads a proof that doesnt start with begin tactic"
        );
    }

    #[test]
    fn test_suppose() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.suppose("suppose n:Nat"),
            Ok(("", Suppose("n".to_string(), VarUse("Nat".to_string())))),
            "Suppose parser doesnt construct the proper node"
        );
        assert!(
            parser
                .suppose("\n\r\t suppose   \t n\t:\t \rNat   ")
                .is_ok(),
            "Suppose parser cant cope with whitespaces"
        );
        assert!(
            parser.suppose("suppose Q : ∀n:Nat. P n").is_ok(),
            "Suppose parser cant cope with more complex type expressions"
        );
        assert!(
            parser.suppose("supposen:Nat").is_err(),
            "Suppose parser doesnt split keyword and variable names"
        );
        assert!(
            parser.parse_tactic("suppose n:Nat").is_ok(),
            "Top level tactic parser doesnt support suppose tactic"
        );
    }
}
//########################### UNIT TESTS

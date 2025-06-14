use super::api::{
    Expression::{
        self, Abstraction, Application, Arrow, Inferator, Match, Pipe,
        TypeProduct, VarUse,
    },
    LofParser,
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, multispace0, multispace1},
    combinator::map,
    multi::{many0, many1},
    sequence::{delimited, preceded},
    IResult,
};

//########################### EXPRESSION PARSERS
impl LofParser {
    pub fn parse_parens<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        delimited(
            preceded(multispace0, char('(')),
            |input| self.parse_expression(input),
            preceded(multispace0, char(')')),
        )(input)
    }
    //
    //
    pub fn parse_var<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        map(
            |input| self.parse_identifier(input),
            |s: &str| VarUse(s.to_string()),
        )(input)
    }
    //
    //
    pub fn parse_abs<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) =
            preceded(multispace0, alt((tag("λ"), tag("\\lambda "))))(input)?;
        let (input, var_name) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        //TODO should allow product type expressions here or only predefined type vars?
        let (input, type_var) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;
        let (input, _) = preceded(multispace0, char('.'))(input)?;
        let (input, body) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;

        Ok((
            input,
            Abstraction(
                var_name.to_string(),
                Box::new(type_var),
                Box::new(body),
            ),
        ))
    }
    //
    //
    pub fn parse_type_abs<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) = preceded(
            multispace0,
            alt((tag("Π"), tag("∀"), tag("\\forall"))),
        )(input)?;
        let (input, var_name) =
            preceded(multispace0, |input| self.parse_identifier(input))(input)?;
        let (input, _) = preceded(multispace0, tag(":"))(input)?;
        //TODO should allow product type expressions here or only predefined type vars?
        let (input, type_var) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;
        let (input, _) = preceded(multispace0, char('.'))(input)?;
        let (input, body) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;

        Ok((
            input,
            TypeProduct(
                var_name.to_string(),
                Box::new(type_var),
                Box::new(body),
            ),
        ))
    }
    //
    //
    pub fn parse_arrow_type<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, domain) = alt((
            |input| self.parse_parens(input),
            |input| self.parse_app(input),
            |input| self.parse_var(input),
        ))(input)?;
        let (input, _) = preceded(multispace0, tag("->"))(input)?;
        let (input, codomain) = self.parse_type_expression(input)?;

        Ok((input, Arrow(Box::new(domain), Box::new(codomain))))
    }
    //
    //
    fn applicable_expression<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        alt((
            |input| self.parse_var(input),
            |input| self.parse_abs(input),
            |input| self.parse_type_abs(input),
            // |input| self.parse_app(input),
            |input| self.parse_parens(input),
        ))(input)
    }
    fn argument_expression<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        alt((
            |input| self.parse_var(input),
            |input| self.parse_meta(input),
            |input| self.parse_parens(input),
        ))(input)
    }
    pub fn parse_app<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, left) =
            preceded(multispace0, |input| self.applicable_expression(input))(
                input,
            )?;
        let (input, args) = many1(preceded(multispace1, |input| {
            self.argument_expression(input)
        }))(input)?;

        Ok((
            input,
            args.into_iter().fold(left, |acc, arg| {
                Application(Box::new(acc), Box::new(arg))
            }),
        ))
    }
    //
    //
    pub fn parse_match_branch<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, (Vec<Expression>, Expression)> {
        let (input, _) = preceded(multispace0, char('|'))(input)?;
        let (input, constructor) =
            preceded(multispace0, |input| self.parse_var(input))(input)?;
        let (input, args) =
            many0(preceded(multispace1, |input| self.parse_var(input)))(input)?;
        let (input, _) = preceded(multispace0, tag("=>"))(input)?;
        let (input, body) =
            preceded(multispace0, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace0, char(','))(input)?;

        let mut pattern = vec![constructor];
        pattern.extend(args);
        Ok((input, (pattern, body)))
    }
    pub fn parse_pattern_match<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) = preceded(multispace0, tag("match"))(input)?;
        let (input, term) =
            preceded(multispace1, |input| self.parse_expression(input))(input)?;
        let (input, _) = preceded(multispace1, tag("with"))(input)?;
        let (input, branches) =
            many1(|input| self.parse_match_branch(input))(input)?;

        Ok((input, Match(Box::new(term), branches)))
    }

    pub fn parse_meta<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        let (input, _) = preceded(multispace0, char('?'))(input)?;

        Ok((input, Inferator()))
    }

    pub fn parse_pipe<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        // TODO should i avoid returning here if there's no '|' ?
        // so this doesnt conflict with other parsers
        let (input, first_type) =
            preceded(multispace0, |input| self.parse_type_expression(input))(
                input,
            )?;

        // parse zero or more additional types separated by '|'
        let (input, other_types) = many1(preceded(
            multispace1,
            preceded(
                tag("|"),
                preceded(multispace0, |input| {
                    self.parse_type_expression(input)
                }),
            ),
        ))(input)?;

        let mut all_types = vec![first_type];
        all_types.extend(other_types);
        Ok((input, Pipe(all_types)))
    }

    pub fn parse_expression<'a>(
        &'a self,
        input: &'a str,
    ) -> IResult<&'a str, Expression> {
        alt((
            |input| self.parse_meta(input),
            |input| self.parse_abs(input),
            |input| self.parse_type_abs(input),
            |input| self.parse_arrow_type(input),
            // application should show up before parse_var
            // otherwise the function will be parsed as normal variable
            // and the rest of the string is not properly parsed
            |input| self.parse_app(input),
            |input| self.parse_pipe(input),
            |input| self.parse_var(input),
            |input| self.parse_parens(input),
            |input| self.parse_pattern_match(input),
        ))(input)
    }
}
//########################### EXPRESSION PARSERS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        config::Config,
        parser::api::{
            Expression::{
                Abstraction, Application, Arrow, Inferator, Match, Pipe,
                TypeProduct, VarUse,
            },
            LofParser,
        },
    };

    #[test]
    fn test_parens() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_parens("(x)").is_ok(),
            "Parser cant cope with parenthesis"
        );
        assert!(
            parser.parse_parens("((x))").is_ok(),
            "Parser cant cope with nested parenthesis"
        );
        assert!(
            parser.parse_parens("(x").is_err(),
            "Parser accepts unmatched parenthesis"
        );
        assert!(
            parser.parse_parens("x)").is_err(),
            "Parser accepts unmatched parenthesis"
        );
        assert_eq!(
            parser.parse_parens("(x)").unwrap(),
            ("", VarUse("x".to_string())),
            "Parenthesis parser doesnt produce subterm properly"
        );
    }

    #[test]
    fn test_type_theory_terms() {
        let parser = LofParser::new(Config::default());
        // variable
        assert!(
            parser.parse_var("test").is_ok(),
            "Parser cant read variables"
        );
        assert_eq!(
            parser.parse_var("  test\n").unwrap(),
            ("\n", VarUse("test".to_string())),
            "Variable parser cant cope with whitespaces"
        );

        // abstraction
        assert!(
            parser.parse_abs("λx:T.x").is_ok(),
            "Parser cant read lambda abstractions"
        );
        assert!(
            parser.parse_abs("λ \tx   :\tT \t . \t x  \n").is_ok(),
            "Abstraction parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_abs("\\lambda   x :T .  x").is_ok(),
            "Abstraction parser cant use 'lambda' keyword"
        );
        assert_eq!(
            parser.parse_abs("λn:nat.n").unwrap(),
            (
                "",
                Abstraction(
                    "n".to_string(),
                    Box::new(VarUse("nat".to_string())),
                    Box::new(VarUse("n".to_string()))
                )
            ),
            "Abstraction struct isnt properly built"
        );

        // type abstraction
        assert!(
            parser.parse_type_abs("ΠT:TYPE.T").is_ok(),
            "Parser cant read type abstractions"
        );
        assert!(
            parser
                .parse_type_abs("Π \tT   :\tTYPE \t . \t T  \n")
                .is_ok(),
            "Type abstraction parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_type_abs("\\forall   T :TYPE .  T").is_ok(),
            "Type abstraction parser cant use 'forall' keyword"
        );
        assert_eq!(
            parser.parse_type_abs("ΠT:TYPE.T").unwrap(),
            (
                "",
                TypeProduct(
                    "T".to_string(),
                    Box::new(VarUse("TYPE".to_string())),
                    Box::new(VarUse("T".to_string()))
                )
            ),
            "Abstraction struct isnt properly built"
        );
    }

    #[test]
    fn test_application() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_app("f x").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    Box::new(VarUse("x".to_string()))
                )
            ),
            "Parser cant read function application"
        );
        assert_eq!(
            parser.parse_expression("f x").unwrap(),
            (
                "",
                Application(
                    Box::new(VarUse("f".to_string())),
                    Box::new(VarUse("x".to_string()))
                )
            ),
            "Expression parser doesnt recognize application"
        );

        assert_eq!(
            parser.parse_app("f x y z").unwrap(),
            (
                "",
                Application(
                    Box::new(Application(
                        Box::new(Application(
                            Box::new(VarUse("f".to_string())),
                            Box::new(VarUse("x".to_string()))
                        )),
                        Box::new(VarUse("y".to_string()))
                    )),
                    Box::new(VarUse("z".to_string()))
                )
            ),
            "Parser should implement left-associative application"
        );

        assert_eq!(
            parser.parse_app("f (x y) z").unwrap(),
            (
                "",
                Application(
                    Box::new(Application(
                        Box::new(VarUse("f".to_string())),
                        Box::new(Application(
                            Box::new(VarUse("x".to_string())),
                            Box::new(VarUse("y".to_string()))
                        ))
                    )),
                    Box::new(VarUse("z".to_string()))
                )
            ),
            "Application parser messes up associativity with parenthesis"
        );
    }

    #[test]
    fn test_arrow_expression() {
        let parser = LofParser::new(Config::default());
        assert_eq!(
            parser.parse_arrow_type("A -> B").unwrap(),
            (
                "",
                Arrow(
                    Box::new(VarUse("A".to_string())),
                    Box::new(VarUse("B".to_string()))
                )
            ),
            "Parser cant read type arrow expressions"
        );
        assert!(
            parser.parse_arrow_type(" \tA   \t \t -> \t B  \n").is_ok(),
            "Arrow expression parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_arrow_type("A->B").is_ok(),
            "Arrow expression parser cant cope with dense notation"
        );
        assert!(
            parser.parse_expression("A->B").is_ok(),
            "Top level parser cant read type arrow expressions"
        );
    }

    #[test]
    fn test_pattern_matching() {
        let parser = LofParser::new(Config::default());
        assert!(
            parser.parse_match_branch("| O => x,").is_ok(),
            "Parser cant read pattern matching branches"
        );
        assert_eq!(
            parser.parse_match_branch("| O => x,").unwrap(),
            ("", (vec![VarUse("O".to_string())], VarUse("x".to_string()))),
            "Pattern match branch isnt properly constructed"
        );
        assert!(
            parser.parse_match_branch("| BinTree l r => x ,").is_ok(),
            "Parser cant read pattern matching branches with variables"
        );

        assert_eq!(
            parser
                .parse_pattern_match("match x with | O => x,")
                .unwrap(),
            (
                "",
                Match(
                    Box::new(VarUse("x".to_string())),
                    vec![(
                        vec![VarUse("O".to_string())],
                        VarUse("x".to_string())
                    )]
                )
            ),
            "Pattern match expression isnt properly constructed"
        );
        assert!(
            parser
                .parse_pattern_match("match \tx   with \n\t|O =>  \nx   , \n ")
                .is_ok(),
            "Pattern match parser cant cope with whitespaces"
        );
        assert!(
            parser.parse_pattern_match("matchx with | O => x,").is_err(),
            "Pattern match parser doesnt split keywords"
        );
        assert!(
            parser.parse_pattern_match("match xwith | O => x,").is_err(),
            "Pattern match parser doesnt split keywords"
        );
    }

    #[test]
    fn test_pipe_expression() {
        let parser = LofParser::new(Config::default());

        assert_eq!(
            parser.parse_pipe("A | B").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Pipe expression for union type isnt working"
        );
        assert_eq!(
            parser.parse_expression("A | B").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Top level expression parser doesnt support pipes"
        );
        assert!(
            parser.parse_pipe(" Variable ").is_err(),
            "Pipe parser shouldnt accept single variable use as type unions"
        );

        assert_eq!(
            parser.parse_pipe("A | B | C | D").unwrap(),
            (
                "",
                Pipe(vec![
                    VarUse("A".to_string()),
                    VarUse("B".to_string()),
                    VarUse("C".to_string()),
                    VarUse("D".to_string()),
                ])
            ),
            "Pipe expression doesnt support n-ary unions"
        );

        assert_eq!(
            parser.parse_pipe("A \n\t \r   |  \n \r\tB").unwrap(),
            (
                "",
                Pipe(vec![VarUse("A".to_string()), VarUse("B".to_string())])
            ),
            "Pipe expression cant cope with whitespaces"
        );
    }

    #[test]
    fn test_infer_operator() {
        let parser = LofParser::new(Config::default());

        assert!(
            parser.parse_meta("?").is_ok(),
            "parser doesnt support the infer operator ?"
        );

        assert!(
            parser.parse_meta("\n  \t\r\r\t  ?").is_ok(),
            "parser doesnt support the infer operator ? preceeded by whitespaces"
        );

        assert!(
            parser.parse_expression("  ? ").is_ok(),
            "top level parser doesnt support the infer operator ?"
        );

        assert_eq!(
            parser.parse_expression("cons ? z l"),
            Ok((
                "",
                Application(
                    Box::new(Application(
                        Box::new(Application(
                            Box::new(VarUse("cons".to_string())),
                            Box::new(Inferator()),
                        )),
                        Box::new(VarUse("z".to_string()))
                    )),
                    Box::new(VarUse("l".to_string()))
                )
            )),
            "Metavariable parser doesnt integrate with applications"
        )
    }
}

use super::{
    api::{parse_source_file, NsAst},
    commons::{parse_optionally_typed_identifier, typed_parameter_list},
};
#[allow(unused_imports)]
use super::{
    api::{Expression, Statement},
    commons::{parse_identifier, parse_type_expression},
    expressions::parse_expression,
};
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag},
    character::complete::{
        char, line_ending, multispace0, multispace1, not_line_ending,
    },
    combinator::opt,
    multi::many0,
    sequence::{delimited, preceded},
    IResult,
};

//########################### STATEMENT PARSERS
//
fn parse_import(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("import"))(input)?;
    let (input, filepath) = preceded(
        multispace0,
        delimited(char('"'), is_not("\""), char('"')),
    )(input)?;

    let (_, ast) = parse_source_file(&format!("{}.lof", filepath));
    match ast {
        NsAst::Stm(file_root_stm) => Ok((input, file_root_stm)),
        NsAst::Exp(_exp) => panic!("fuck this type system fr"),
    }
}
//
//
pub fn parse_let(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("let"))(input)?;
    let (input, (var_name, opt_type)) =
        preceded(multispace1, parse_optionally_typed_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":="))(input)?;
    let (input, term) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    Ok((
        input,
        Statement::Let(var_name.to_string(), opt_type, Box::new(term)),
    ))
}
//
//
pub fn parse_function(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("fun"))(input)?;
    let (input, is_rec) = opt(preceded(multispace1, tag("rec")))(input)?;
    let is_rec = is_rec.is_some();

    let (input, fun_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, args) = typed_parameter_list(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, output_type) =
        preceded(multispace1, parse_type_expression)(input)?;

    let (input, _) = preceded(multispace0, tag("{"))(input)?;
    let (input, body) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, tag("}"))(input)?;

    Ok((
        input,
        Statement::Fun(
            fun_name.to_string(),
            args,
            Box::new(output_type),
            Box::new(body),
            is_rec,
        ),
    ))
}
//
//
pub fn parse_theorem(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(
        multispace0,
        alt((tag("theorem"), tag("lemma"), tag("proposition"))),
    )(input)?;
    let (input, theorem_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, formula) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, tag(":="))(input)?;
    let (input, proof) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, tag("qed."))(input)?;

    Ok((
        input,
        Statement::Let(
            theorem_name.to_string(),
            Some(formula),
            Box::new(proof),
        ),
    ))
}
//
//
pub fn parse_comment(input: &str) -> IResult<&str, Statement> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("#")(input)?;
    let (input, _) = not_line_ending(input)?;
    let (input, _) = opt(line_ending)(input)?;

    Ok((input, Statement::Comment()))
}
//
//
pub fn parse_axiom(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("axiom"))(input)?;
    let (input, axiom_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, formula) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    Ok((
        input,
        Statement::Axiom(axiom_name.to_string(), Box::new(formula)),
    ))
}
//
//
pub fn parse_inductive_constructor(
    input: &str,
) -> IResult<&str, (String, Expression)> {
    let (input, _) = preceded(multispace0, char('|'))(input)?;
    let (input, constructor_name) =
        preceded(multispace0, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, constructor_type) = parse_type_expression(input)?;

    Ok((input, (constructor_name.to_string(), constructor_type)))
}
pub fn parse_inductive_def(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("inductive"))(input)?;
    let (input, inductive_type_name) =
        preceded(multispace1, parse_identifier)(input)?;
    let (input, parameters) = typed_parameter_list(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, ariety) = preceded(multispace0, parse_type_expression)(input)?;
    let (input, _) = preceded(multispace0, tag("{"))(input)?;
    let (input, constructors) = many0(parse_inductive_constructor)(input)?;
    let (input, _) = preceded(multispace0, char('}'))(input)?;

    Ok((
        input,
        Statement::Inductive(
            inductive_type_name.to_string(),
            parameters,
            Box::new(ariety),
            constructors,
        ),
    ))
}
//
//
pub fn parse_statement(input: &str) -> IResult<&str, Statement> {
    alt((
        parse_comment,
        parse_let,
        parse_axiom,
        parse_inductive_def,
        parse_theorem,
        parse_function,
        parse_import,
    ))(input)
}
//
//########################### STATEMENT PARSERS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::parser::{
        api::Expression::{Application, Arrow, VarUse},
        api::Statement,
        api::Statement::{Axiom, Comment, Inductive, Let},
        statements::{
            parse_axiom, parse_comment, parse_function, parse_import,
            parse_inductive_def, parse_let, parse_statement, parse_theorem,
        },
    };

    #[test]
    fn test_comments() {
        assert!(parse_comment("#abc\n").is_ok(), "Parser cant read comments");
        assert!(
            parse_comment("#abc").is_ok(),
            "Parser cant read comments at end of input"
        );
        assert_eq!(
            parse_comment("#abc").unwrap(),
            ("", Comment()),
            "Comment node isnt properly constructed"
        );
    }

    #[test]
    fn test_let() {
        assert!(
            parse_let("let n: nat := x;").is_ok(),
            "Parser cant read let definitions"
        );
        assert!(
            parse_let("let \t n  \t:  \t nat  :=\t  x  \t;").is_ok(),
            "Let parser cant cope with multispaces"
        );
        assert!(
            parse_let("letn :nat:= x;").is_err(),
            "Let parser doesnt split 'let' keyword and variable identifier"
        );
        assert_eq!(
            parse_let("let n : nat := x;").unwrap(),
            (
                "",
                Let(
                    "n".to_string(),
                    Some(VarUse("nat".to_string())),
                    Box::new(VarUse("x".to_string()))
                )
            ),
            "Let definition struct isnt properly constructed"
        );
        assert!(
            parse_statement("let n: nat := x;").is_ok(),
            "Top level parser can't read let definitions"
        );
    }

    #[test]
    fn test_parse_function() {
        assert_eq!(
            parse_function("fun f (n: Nat): Nat { s n }"),
            Ok((
                "",
                Statement::Fun(
                    "f".to_string(),
                    vec![("n".to_string(), VarUse("Nat".to_string()))],
                    Box::new(VarUse("Nat".to_string())),
                    Box::new(Application(
                        Box::new(VarUse("s".to_string())),
                        Box::new(VarUse("n".to_string()))
                    )),
                    false
                )
            )),
            "Function parser doesnt construct the statement properly"
        );
        assert_eq!(
            parse_function("fun rec f (n: Nat): Nat { f n }"),
            Ok((
                "",
                Statement::Fun(
                    "f".to_string(),
                    vec![("n".to_string(), VarUse("Nat".to_string()))],
                    Box::new(VarUse("Nat".to_string())),
                    Box::new(Application(
                        Box::new(VarUse("f".to_string())),
                        Box::new(VarUse("n".to_string()))
                    )),
                    true
                )
            )),
            "Function parser doesnt recognize recursive functions"
        );

        assert_eq!(
            parse_function("fun f : TYPE { TYPE }"),
            Ok((
                "",
                Statement::Fun(
                    "f".to_string(),
                    vec![],
                    Box::new(VarUse("TYPE".to_string())),
                    Box::new(VarUse("TYPE".to_string())),
                    false
                )
            )),
            "Function parser cant cope with functions with no arguments"
        );
        assert_eq!(
            parse_function("fun f (l: List Nat): List Nat { l }"),
            Ok((
                "",
                Statement::Fun(
                    "f".to_string(),
                    vec![(
                        "l".to_string(),
                        Application(
                            Box::new(VarUse("List".to_string())),
                            Box::new(VarUse("Nat".to_string()))
                        )
                    )],
                    Box::new(Application(
                        Box::new(VarUse("List".to_string())),
                        Box::new(VarUse("Nat".to_string()))
                    )),
                    Box::new(VarUse("l".to_string())),
                    false
                )
            )),
            "Function parser cant cope with arguments that have application types"
        );
        assert!(
            parse_function(
                "fun  \t \r f \r  \t  ( \t\r x \r\t :  \tNat  )  :  Nat  {  x  }"
            )
            .is_ok(),
            "Function parser cant cope with whitespaces"
        );
        assert!(
            parse_statement("fun f (l: List Nat): List Nat { l }").is_ok(),
            "Top level stm parser doesnt recognize functions"
        );

        assert!(
            parse_function("rec f : TYPE { TYPE }").is_err(),
            "Function parser accepts function with no 'fun' keyword"
        );
        assert!(
            parse_function("fun rec (x: TYPE): TYPE { TYPE }").is_err(),
            "Function parser accepts function with no name"
        );
        assert!(
            parse_function("fun rec myFunction (x: TYPE) { TYPE}").is_err(),
            "Function parser accepts function with no return type"
        );
        assert!(
            parse_function("fun rec myFunction(x: Int): Int").is_err(),
            "Function parser accepts function with no body"
        );
    }

    #[test]
    fn test_axiom() {
        assert!(
            parse_axiom("axiom nat:TYPE;").is_ok(),
            "Parser cant read axioms"
        );
        assert!(
            parse_axiom("axiom  nat :\tTYPE  ;").is_ok(),
            "Axiom parser cant cope with multispaces"
        );
        assert!(
            parse_axiom("axiomnat:TYPE;").is_err(),
            "Axiom parser doesnt split 'axiom' keyword and axiom identifier"
        );
        assert_eq!(
            parse_axiom("axiom nat : TYPE;").unwrap(),
            (
                "",
                Axiom("nat".to_string(), Box::new(VarUse("TYPE".to_string())))
            ),
            "Axiom node isnt properly constructed"
        );
        assert!(
            parse_statement("axiom nat:TYPE;").is_ok(),
            "Top level parser can't read axioms"
        );
    }

    #[test]
    fn test_theorem() {
        assert_eq!(
            parse_theorem("theorem p : PROP := p qed.").unwrap(),
            (
                "",
                Statement::Let(
                    "p".to_string(),
                    Some(VarUse("PROP".to_string())),
                    Box::new(VarUse("p".to_string())),
                )
            ),
            "Parser cant theorem proofs"
        );
        assert!(
            parse_theorem("theorem   \tp\t  : \t PROP :=\n\t  p \n\tqed.")
                .is_ok(),
            "Theorem parser cant cope with whitespaces"
        );
        assert!(
            parse_theorem("lemma p : PROP := p qed.").is_ok(),
            "Theorem parser doesnt support 'lemma' keyword"
        );
        assert!(
            parse_theorem("proposition p : PROP := p qed.").is_ok(),
            "Theorem parser doesnt support 'proposition' keyword"
        );
        assert!(
            parse_theorem("theoremp : PROP := pqed.").is_err(),
            "Theorem parser doesnt split the keywords"
        );
        assert!(
            parse_theorem("theorem p:PROP:=p qed.").is_ok(),
            "Theorem parser doesnt accept dense text"
        );
    }

    #[test]
    fn test_inductive() {
        let test_definition = Inductive(
            "nat".to_string(),
            vec![],
            Box::new(VarUse("TYPE".to_string())),
            vec![
                ("o".to_string(), VarUse("nat".to_string())),
                (
                    "s".to_string(),
                    Arrow(
                        Box::new(VarUse("nat".to_string())),
                        Box::new(VarUse("nat".to_string())),
                    ),
                ),
            ],
        );

        assert_eq!(
            parse_inductive_def(
                "inductive nat : TYPE { \n| o: nat \n| \ts : nat -> nat}"
            )
            .unwrap(),
            ("", test_definition.clone()),
            "Parser cant read inductive definitions"
        );
        assert!(
            parse_inductive_def("inductive Empty : TYPE {} ").is_ok(),
            "Inductive parser doesnt support the Empty type"
        );
        assert_eq!(
            parse_inductive_def("inductive nat:TYPE{|o:nat|s:nat->nat}")
                .unwrap(),
            ("", test_definition.clone()),
            "Inductive parser cant cope with dense notation"
        );
        assert!(
            parse_inductive_def("inductivenat:TYPE{|o: nat|s : nat-> nat}").is_err(),
            "Inductive parser doesnt expect a whitespace after the inductive keyword"
        );
        assert_eq!(
            parse_inductive_def(
                "inductive T : TYPE { | c: (list nat) -> T | g: nat -> nat -> T}"
            )
            .unwrap(),
            (
                "",
                Statement::Inductive(
                    "T".to_string(),
                    vec![],
                    Box::new(VarUse("TYPE".to_string())),
                    vec![
                        (
                            "c".to_string(),
                            Arrow(
                                Box::new(Application(
                                    Box::new(VarUse(
                                        "list".to_string()
                                    )),
                                    Box::new(VarUse("nat".to_string())),
                                )),
                                Box::new(VarUse("T".to_string()))
                            )
                        ),
                        (
                            "g".to_string(),
                            Arrow(
                                Box::new(VarUse("nat".to_string())),
                                Box::new(Arrow(
                                    Box::new(VarUse("nat".to_string())),
                                    Box::new(VarUse("T".to_string())),
                                ))
                            ),
                        ),
                    ],
                )
            ),
            "Inductive constructor parser cant properly parse constructor types"
        );
        assert!(
            parse_statement(
                "inductive T: TYPE { \n\t| c:(list nat) ->T \n\t| g: nat -> nat->T}"
            )
            .is_ok(),
            "Top level parser cant parse inductive definitions"
        );

        assert!(
            parse_inductive_def(
                "inductive list (T: TYPE) : TYPE { |nil: (list T) |cons: T -> (list T) }"
            )
            .is_ok(),
            "Inductive parser doesnt support polymorphic types"
        );
        assert!(
            parse_inductive_def(
                "inductive le : nat -> nat -> PROP { |lez: PROP | leS : PROP}"
            )
            .is_ok(),
            "Inductive parser doesnt support complex arieties"
        );
        assert!(
            parse_inductive_def(
                "inductive eq (T:TYPE) (x:T) : T -> PROP { |refl: (((eq T) x) x)}"
            )
            .is_ok(),
            "Inductive parser doesnt support Leibniz equality definition"
        );
    }

    #[test]
    fn test_import() {
        assert!(
            parse_import("import \"library/logic\"").is_ok(),
            "Import parser isnt working"
        );
        assert!(
            parse_statement("import \"library/logic\"").is_ok(),
            "Top level statement parser doesnt support import"
        );
    }
}

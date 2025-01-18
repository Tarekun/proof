use crate::{
    parser::api::Statement,
    type_theory::environment::{self, Environment},
};
use std::collections::VecDeque;

#[derive(Debug)]
pub enum ProgramNode<Term> {
    OfStm(Statement),
    OfTerm(Term),
}

pub struct Program<Term /*, F1, F2*/>
where
    Term: Clone,
    // F1: Fn(&Term) -> Term,
    // F2: Fn(&Statement) -> (),
{
    schedule: VecDeque<ProgramNode<Term>>,
    // reduce_term: F1,
    // evaluate_statement: F2,
}

impl<Term /*, F1, F2*/> Program<Term /*, F1, F2*/>
where
    Term: Clone,
    // F1: Fn(&Term) -> Term,
    // F2: Fn(&Statement) -> (),
{
    pub fn new(/*reduce_term: F1, evaluate_statement: F2*/) -> Self {
        Program {
            schedule: VecDeque::new(),
            // reduce_term,
            // evaluate_statement,
        }
    }

    /// Add a new statement to the queue
    pub fn push_statement(&mut self, statement: &Statement) {
        self.schedule
            .push_back(ProgramNode::OfStm(statement.clone()));
    }

    /// Add a new term to the queue
    pub fn push_term(&mut self, term: &Term) {
        self.schedule.push_back(ProgramNode::OfTerm(term.clone()));
    }

    pub fn schedule_iterable(
        &self,
    ) -> std::collections::vec_deque::Iter<'_, ProgramNode<Term>> {
        self.schedule.iter()
    }

    /// Execute the prorgam schedule
    pub fn execute(&self) -> Result<(), String> {
        for node in &self.schedule {
            // match node {
            //     ProgramNode::OfTerm(term) => {
            //         let _normal_form = (self.reduce_term)(term);
            //         //TODO do something with the result
            //     }
            //     ProgramNode::OfStm(stm) => {
            //         let _ = (self.evaluate_statement)(stm);
            //     }
            // }
        }

        Ok(())
    }
}

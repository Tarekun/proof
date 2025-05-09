use crate::runtime::program::ProgramNode::{OfStm, OfTerm};
use crate::type_theory::{environment::Environment, interface::TypeTheory};
use std::collections::VecDeque;

#[derive(Debug, PartialEq)]
pub enum ProgramNode<Term, Stm> {
    OfStm(Stm),
    OfTerm(Term),
}

pub struct Program<T>
where
    T: TypeTheory,
{
    schedule: VecDeque<ProgramNode<T::Term, T::Stm>>,
    pub environment: Environment<T::Term, T::Type>,
}

impl<T> Program<T>
where
    T: TypeTheory,
{
    pub fn new() -> Self {
        Program {
            schedule: VecDeque::new(),
            environment: T::default_environment(),
        }
    }

    /// Add a new statement to the queue
    pub fn push_statement(&mut self, statement: &T::Stm) {
        self.schedule
            .push_back(ProgramNode::OfStm(statement.clone()));
    }

    /// Add a new term to the queue
    pub fn push_term(&mut self, term: &T::Term) {
        self.schedule.push_back(ProgramNode::OfTerm(term.clone()));
    }

    pub fn schedule_iterable(
        &self,
    ) -> std::collections::vec_deque::Iter<'_, ProgramNode<T::Term, T::Stm>>
    {
        self.schedule.iter()
    }

    pub fn peek_top_schedule(&self) -> Option<&ProgramNode<T::Term, T::Stm>> {
        self.schedule.back()
    }

    /// Execute the prorgam schedule
    pub fn execute(&mut self) -> Result<(), String> {
        for node in &self.schedule {
            match node {
                OfTerm(term) => {
                    let _normal_form =
                        T::normalize_term(&mut self.environment, term);
                    //TODO do something with the result
                }
                OfStm(stm) => {
                    let _ = T::evaluate_statement(&mut self.environment, stm);
                }
            }
        }

        Ok(())
    }
}

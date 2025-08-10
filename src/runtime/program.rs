use crate::runtime::program::ProgramNode::{OfStm, OfTerm};
use crate::type_theory::{
    environment::Environment,
    interface::{Reducer, TypeTheory},
};
use std::collections::VecDeque;

#[derive(Clone, Debug, PartialEq)]
pub enum ProgramNode<Term, Stm> {
    OfStm(Stm),
    OfTerm(Term),
}

pub struct Schedule<T: TypeTheory> {
    schedule: VecDeque<ProgramNode<T::Term, T::Stm>>,
}

impl<T: TypeTheory> Schedule<T> {
    pub fn new() -> Self {
        Self {
            schedule: VecDeque::new(),
        }
    }

    pub fn add_statement(&mut self, statement: &T::Stm) {
        self.schedule
            .push_back(ProgramNode::OfStm(statement.clone()));
    }

    pub fn add_expression(&mut self, term: &T::Exp) {
        self.schedule.push_back(ProgramNode::OfTerm(term.clone()));
    }
}

pub struct Program<T>
where
    T: TypeTheory,
{
    schedule: Schedule<T>,
    pub environment: Environment<T::Term, T::Type>,
}

impl<T> Program<T>
where
    T: TypeTheory + Reducer,
{
    pub fn new() -> Self {
        Program {
            schedule: Schedule::new(),
            environment: T::default_environment(),
        }
    }
    pub fn with_schedule(schedule: Schedule<T>) -> Self {
        Program {
            schedule,
            environment: T::default_environment(),
        }
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

    // TODO: this should handle both terms and type expressions
    pub fn execute_expression(
        &mut self,
        exp: &T::Term,
    ) -> Result<T::Term, String> {
        //TODO do something with the result
        Ok(T::normalize_term(&mut self.environment, exp))
    }

    pub fn execute_statement(&mut self, stm: &T::Stm) -> Result<(), String> {
        let _ = T::evaluate_statement(&mut self.environment, stm);
        Ok(())
    }

    /// Execute the prorgam schedule
    pub fn execute(&mut self) -> Result<(), String> {
        let schedule = self.schedule.clone();
        for node in schedule {
            match node {
                OfTerm(term) => {
                    let _normal_form = self.execute_expression(&term)?;
                }
                OfStm(stm) => {
                    let _ = self.execute_statement(&stm)?;
                }
            }
        }

        Ok(())
    }
}

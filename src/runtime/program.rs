use std::collections::VecDeque;

use crate::type_theory::interface::TypeTheory;

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
}

impl<T> Program<T>
where
    T: TypeTheory,
{
    pub fn new(/*reduce_term: F1, evaluate_statement: F2*/) -> Self {
        Program {
            schedule: VecDeque::new(),
            // reduce_term,
            // evaluate_statement,
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
    pub fn execute(&self) -> Result<(), String> {
        let mut runtime_env = T::default_environment();
        for node in &self.schedule {
            match node {
                ProgramNode::OfTerm(term) => {
                    let _normal_form = T::reduce_term(&mut runtime_env, term);
                    //TODO do something with the result
                }
                ProgramNode::OfStm(stm) => {
                    let _ = T::evaluate_statement(&mut runtime_env, stm);
                }
            }
        }

        Ok(())
    }
}

use std::collections::VecDeque;

#[derive(Debug, PartialEq)]
pub enum ProgramNode<Term, Stm> {
    OfStm(Stm),
    OfTerm(Term),
}

pub struct Program<Term, Stm /*, F1, F2*/>
where
    Term: Clone,
    Stm: Clone,
    // F1: Fn(&Term) -> Term,
    // F2: Fn(&Statement) -> (),
{
    schedule: VecDeque<ProgramNode<Term, Stm>>,
    // reduce_term: F1,
    // evaluate_statement: F2,
}

impl<Term, Stm /*, F1, F2*/> Program<Term, Stm /*, F1, F2*/>
where
    Term: Clone,
    Stm: Clone,
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
    pub fn push_statement(&mut self, statement: &Stm) {
        self.schedule
            .push_back(ProgramNode::OfStm(statement.clone()));
    }

    /// Add a new term to the queue
    pub fn push_term(&mut self, term: &Term) {
        self.schedule.push_back(ProgramNode::OfTerm(term.clone()));
    }

    pub fn schedule_iterable(
        &self,
    ) -> std::collections::vec_deque::Iter<'_, ProgramNode<Term, Stm>> {
        self.schedule.iter()
    }

    pub fn peek_top_schedule(&self) -> Option<&ProgramNode<Term, Stm>> {
        self.schedule.back()
    }

    /// Execute the prorgam schedule
    pub fn execute(&self) -> Result<(), String> {
        for node in &self.schedule {
            match node {
                ProgramNode::OfTerm(term) => {
                    let _normal_form = (self.reduce_term)(term);
                    //TODO do something with the result
                }
                ProgramNode::OfStm(stm) => {
                    let _ = (self.evaluate_statement)(stm);
                }
            }
        }

        Ok(())
    }
}

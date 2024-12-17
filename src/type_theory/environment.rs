use std::collections::HashMap;
use crate::type_theory::stlc::StlcTerm;

#[derive(Debug, Default)]
pub struct Context {
    pub variables: HashMap<String, StlcTerm>,
}

impl Context {
    // Add a new variable to the context
    pub fn add_variable(&mut self, name: String, term: StlcTerm) {
        self.variables.insert(name, term);
    }

    // Retrieve a variable from the context
    pub fn get_variable(&self, name: &str) -> Option<&StlcTerm> {
        self.variables.get(name)
    }

    pub fn is_bound(&self, name: &str) -> bool {
        self.variables.contains_key(name)
    }
}

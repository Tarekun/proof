
use std::collections::HashMap;
use crate::type_theory::stlc::StlcTerm;


#[derive(Debug, Default)]
pub struct Environment {
    pub context: HashMap<String, StlcTerm>, //var_name, type
    pub deltas: HashMap<String, StlcTerm>,  //var_name, term
}

impl Environment {
    // Add a new variable to the context
    pub fn add_variable_definition(&mut self, name: &str, term: StlcTerm) {
        self.deltas.insert(name.to_string(), term);
    }

    pub fn add_variable_to_context(&mut self, name: &str, type_term: StlcTerm) {
        self.context.insert(name.to_string(), type_term);
    }

    pub fn get_from_context(&self, name: &str) -> Option<(&str, &StlcTerm)> {
        self.context.get(name).map(|type_term| (name, type_term))
    }

    pub fn get_from_deltas(&self, name: &str) -> Option<(&str, &StlcTerm)> {
        self.deltas.get(name).map(|body| (name, body))
        // match self.deltas.get(name) {
        //     Some(body) => Some((name, body)),
        //     None => None,
        // }
    }

    pub fn is_bound(&self, name: &str) -> bool {
        match self.get_from_context(&name) {
            Some(_) => true,
            None => match self.get_from_deltas(&name) {
                Some(_) => true,
                None => false,
            },
        }
    }
}

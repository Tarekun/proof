use crate::type_theory::stlc::StlcTerm;
use std::collections::HashMap;

#[derive(Debug, Default, Clone)]
pub struct Environment {
    pub context: HashMap<String, StlcTerm>, //var_name, type
    pub deltas: HashMap<String, StlcTerm>,  //var_name, term
}

impl Environment {
    // Add a new variable to the context
    pub fn add_variable_definition(&mut self, name: &str, term: &StlcTerm) {
        //TODO avoid cloning?
        self.deltas.insert(name.to_string(), term.clone());
    }

    pub fn add_variable_to_context(
        &mut self,
        name: &str,
        type_term: &StlcTerm,
    ) {
        //TODO avoid cloning?
        self.context.insert(name.to_string(), type_term.clone());
    }

    pub fn get_from_context<'a>(
        &'a self,
        name: &'a str,
    ) -> Option<(&'a str, &'a StlcTerm)> {
        self.context.get(name).map(|type_term| (name, type_term))
    }

    pub fn get_from_deltas<'a>(
        &'a self,
        name: &'a str,
    ) -> Option<(&'a str, &'a StlcTerm)> {
        self.deltas.get(name).map(|body| (name, body))
    }
}

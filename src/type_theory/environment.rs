use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Environment<TermType> {
    pub context: HashMap<String, TermType>, //var_name, type
    pub deltas: HashMap<String, TermType>,  //var_name, term
}

impl<TermType: Clone> Environment<TermType> {
    pub fn new() -> Self {
        Self {
            context: HashMap::new(),
            deltas: HashMap::new(),
        }
    }

    /// Define a new variable adding it to the delta substitution context, along with
    /// its definition body
    pub fn add_variable_definition(&mut self, name: &str, term: &TermType) {
        //TODO avoid cloning?
        self.deltas.insert(name.to_string(), term.clone());
    }

    /// Insert a new typed variable into the context
    pub fn add_variable_to_context(
        &mut self,
        name: &str,
        type_term: &TermType,
    ) {
        //TODO avoid cloning?
        self.context.insert(name.to_string(), type_term.clone());
    }

    pub fn get_from_context<'a>(
        &'a self,
        name: &'a str,
    ) -> Option<(&'a str, &'a TermType)> {
        self.context.get(name).map(|type_term| (name, type_term))
    }

    pub fn get_from_deltas<'a>(
        &'a self,
        name: &'a str,
    ) -> Option<(&'a str, &'a TermType)> {
        self.deltas.get(name).map(|body| (name, body))
    }
}

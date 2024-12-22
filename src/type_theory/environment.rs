use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Environment<TermType> {
    pub context: HashMap<String, TermType>, //var_name, variable type
    pub deltas: HashMap<String, (TermType, TermType)>, //var_name, definition term
}

//TODO check if this cloning is really necessary or there's better ways
impl<TermType: Clone> Environment<TermType> {
    pub fn new() -> Self {
        Self {
            context: HashMap::new(),
            deltas: HashMap::new(),
        }
    }

    pub fn with_defaults(
        axioms: Vec<(&str, &TermType)>,
        deltas: Vec<(&str, (&TermType, &TermType))>,
    ) -> Self {
        let mut context_map = HashMap::new();
        let mut deltas_map = HashMap::new();

        for (name, term) in axioms {
            context_map.insert(name.to_string(), term.clone());
        }
        for (name, (term, term_type)) in deltas {
            deltas_map
                .insert(name.to_string(), (term.clone(), term_type.clone()));
        }

        Self {
            context: context_map,
            deltas: deltas_map,
        }
    }

    /// Define a new variable adding it to the delta substitution context, along with
    /// its definition body
    pub fn add_variable_definition(
        &mut self,
        name: &str,
        term: &TermType,
        term_type: &TermType,
    ) {
        //TODO avoid cloning?
        self.deltas
            .insert(name.to_string(), (term.clone(), term_type.clone()));
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
    ) -> Option<(&'a str, &'a (TermType, TermType))> {
        self.deltas.get(name).map(|body| (name, body))
    }
}

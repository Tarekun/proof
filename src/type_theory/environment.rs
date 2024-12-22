use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Environment<Term, Type> {
    pub context: HashMap<String, Type>, //var_name, variable type
    pub deltas: HashMap<String, (Term, Type)>, //var_name, definition term
}

//TODO check if this cloning is really necessary or there's better ways
impl<Term: Clone, Type: Clone> Environment<Term, Type> {
    pub fn with_defaults(
        axioms: Vec<(&str, &Type)>,
        deltas: Vec<(&str, &Term, &Type)>,
    ) -> Self {
        let mut context_map = HashMap::new();
        let mut deltas_map = HashMap::new();

        for (name, term) in axioms {
            context_map.insert(name.to_string(), term.clone());
        }
        for (name, term, term_type) in deltas {
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
        term: &Term,
        term_type: &Type,
    ) {
        //TODO avoid cloning?
        self.deltas
            .insert(name.to_string(), (term.clone(), term_type.clone()));
    }

    /// Insert a new typed variable into the context
    pub fn add_variable_to_context(&mut self, name: &str, type_term: &Type) {
        //TODO avoid cloning?
        self.context.insert(name.to_string(), type_term.clone());
    }

    pub fn get_from_context<'a>(
        &'a self,
        name: &'a str,
    ) -> Option<(&'a str, &'a Type)> {
        self.context.get(name).map(|type_term| (name, type_term))
    }

    pub fn get_from_deltas<'a>(
        &'a self,
        name: &'a str,
    ) -> Option<(&'a str, &'a (Term, Type))> {
        self.deltas.get(name).map(|body| (name, body))
    }
}

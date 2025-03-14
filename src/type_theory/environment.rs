use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Environment<Term, Type> {
    pub context: HashMap<String, Type>, //var_name, variable type
    pub deltas: HashMap<String, (Term, Type)>, //var_name, definition term, type
    pub atomic_types: HashMap<String, Type>, //type_name, type_obj
}

//TODO check if this cloning is really necessary or there's better ways
impl<Term: Clone, Type: Clone + PartialEq> Environment<Term, Type> {
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
            atomic_types: HashMap::new(),
        }
    }
    pub fn with_defaults_lower_order(
        axioms: Vec<(&str, &Type)>,
        deltas: Vec<(&str, &Term, &Type)>,
        types: Vec<(&str, &Type)>,
    ) -> Self {
        let mut context_map = HashMap::new();
        let mut deltas_map = HashMap::new();
        let mut atomic_types_map = HashMap::new();

        for (name, term) in axioms {
            context_map.insert(name.to_string(), term.clone());
        }
        for (name, term, term_type) in deltas {
            deltas_map
                .insert(name.to_string(), (term.clone(), term_type.clone()));
        }
        for (name, type_obj) in types {
            atomic_types_map.insert(name.to_string(), type_obj.clone());
        }

        Self {
            context: context_map,
            deltas: deltas_map,
            atomic_types: atomic_types_map,
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

    fn remove_variable_definition(&mut self, name: &str) {
        self.deltas.remove(name);
    }

    /// Insert a new typed variable into the context
    pub fn add_variable_to_context(&mut self, name: &str, type_term: &Type) {
        //TODO avoid cloning?
        //TODO check the type_term exists?
        self.context.insert(name.to_string(), type_term.clone());
    }

    /// Remove a variable from the context
    fn remove_variable_from_context(&mut self, name: &str) {
        self.context.remove(name);
    }

    /// Add a local variable to the context, execute a closure, and then remove the variable
    pub fn with_local_declaration<F, R>(
        &mut self,
        name: &str,
        type_term: &Type,
        callable: F,
    ) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.add_variable_to_context(name, type_term);
        let result = callable(self);
        self.remove_variable_from_context(name);

        result
    }

    /// Add a local variable substitution (ie definition) to the deltas, execute a closure,
    /// and then remove the variable
    pub fn with_local_substitution<F, R>(
        &mut self,
        name: &str,
        term: &Term,
        term_type: &Type,
        callable: F,
    ) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        self.add_variable_definition(name, term, term_type);
        let result = callable(self);
        self.remove_variable_definition(name);

        result
    }

    /// Add a list of local variables to the context, execute a closure, and then remove the variables
    pub fn with_local_declarations<F, R>(
        &mut self,
        assumptions: &[(String, Type)],
        callable: F,
    ) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        if assumptions.is_empty() {
            callable(self)
        } else {
            let ((name, type_term), rest) = assumptions.split_first().unwrap();
            self.add_variable_to_context(name, type_term);
            let result = self.with_local_declarations(rest, callable);
            self.remove_variable_from_context(name);

            result
        }
    }

    /// Add a list of local variables to the context, execute a closure, and then remove the variables
    pub fn with_local_substitutions<F, R>(
        &mut self,
        substitutions: &[(String, Term, Type)],
        callable: F,
    ) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        if substitutions.is_empty() {
            callable(self)
        } else {
            let ((name, term, term_type), rest) =
                substitutions.split_first().unwrap();
            self.add_variable_definition(name, term, term_type);
            let result = self.with_local_substitutions(rest, callable);
            self.remove_variable_definition(name);

            result
        }
    }

    /// Runs a callable under a local environment which is a rollbackable copy
    /// of `self` that can be mutated without staining the original environment
    pub fn with_rollback<F, R>(&mut self, callable: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let mut cloned = self.clone();
        let result = callable(&mut cloned);

        result
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
        self.deltas
            .get(name)
            .map(|typed_body: &(Term, Type)| (name, typed_body))
    }

    pub fn get_atomic_type<'a>(
        &'a self,
        type_name: &'a str,
    ) -> Option<(&'a str, &'a Type)> {
        self.atomic_types
            .get(type_name)
            .map(|type_obj| (type_name, type_obj))
    }

    pub fn is_var_bound(&self, var_name: &str) -> bool {
        match self.get_from_context(var_name) {
            Some(_) => true,
            None => match self.get_from_deltas(var_name) {
                Some(_) => true,
                None => false,
            },
        }
    }

    pub fn get_variable_type(&self, var_name: &str) -> Option<Type> {
        match self.get_from_context(var_name) {
            Some((_, var_type)) => Some(var_type.clone()),
            None => match self.get_from_deltas(var_name) {
                Some((_, (_, var_type))) => Some(var_type.clone()),
                None => None,
            },
        }
    }
}

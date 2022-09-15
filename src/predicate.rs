use crate::Domain;
use biodivine_lib_bdd::{BddValuation, BddVariable, BddVariableSet, BddVariableSetBuilder};

/// A predicate maps values from [`Domain`] to a boolean value.
pub trait Predicate<D: Domain>: 'static {
    fn eval(&self, value: &D) -> bool;
}

/// A predicate representing an equality constraint over the provided value.
#[derive(Debug)]
struct EqPredicate<D: Domain + PartialEq> {
    value: D,
}

impl<D: Domain + PartialEq> Predicate<D> for EqPredicate<D> {
    fn eval(&self, value: &D) -> bool {
        self.value == *value
    }
}

impl<D: Domain, F: Fn(&D) -> bool + 'static> Predicate<D> for F {
    fn eval(&self, value: &D) -> bool {
        self(value)
    }
}

/// A predicate computed by the provided closure.
pub struct ClosurePredicate<D: Domain> {
    pub(crate) name: &'static str,
    pub(crate) closure: Box<dyn Fn(&D) -> bool + 'static>,
}

impl<D: Domain> Predicate<D> for ClosurePredicate<D> {
    fn eval(&self, value: &D) -> bool {
        (self.closure)(value)
    }
}

impl<D: Domain> std::fmt::Display for ClosurePredicate<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

pub struct PredicatesBuilder<D: Domain>(Vec<ClosurePredicate<D>>);

pub struct Predicates<D: Domain> {
    predicates: Vec<ClosurePredicate<D>>,
    variables: Vec<BddVariable>,
    manager: BddVariableSet,
}

impl<D: Domain> Default for PredicatesBuilder<D> {
    fn default() -> Self {
        Self(Vec::default())
    }
}

impl<D: Domain> Predicates<D> {
    #[must_use]
    pub fn builder() -> PredicatesBuilder<D> {
        PredicatesBuilder::default()
    }

    pub(crate) fn evaluate(&self, observation: &D) -> BddValuation {
        BddValuation::new(
            self.predicates
                .iter()
                .map(|predicate| predicate.eval(observation))
                .collect(),
        )
    }

    pub(crate) fn bdd_variable(&self, predicate: PredicateId) -> BddVariable {
        self.variables[predicate.0]
    }

    pub(crate) fn bdd_manager(&self) -> &BddVariableSet {
        &self.manager
    }
}

impl<D: Domain> PredicatesBuilder<D> {
    pub fn new_predicate(&mut self, predicate: ClosurePredicate<D>) -> PredicateId {
        let id = PredicateId(self.0.len());
        self.0.push(predicate);
        id
    }

    #[must_use]
    pub fn build(self) -> Predicates<D> {
        let mut builder = BddVariableSetBuilder::new();
        let variables = self
            .0
            .iter()
            .map(|proposition| builder.make_variable(&format!("{proposition}")))
            .collect();
        Predicates {
            predicates: self.0,
            variables,
            manager: builder.build(),
        }
    }
}

impl<D: Domain> std::ops::Index<PredicateId> for Predicates<D> {
    type Output = ClosurePredicate<D>;

    fn index(&self, index: PredicateId) -> &Self::Output {
        &self.predicates[index.0]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PredicateId(usize);

impl PredicateId {
    #[cfg(test)]
    pub(crate) fn new_unchecked(val: usize) -> Self {
        Self(val)
    }
}

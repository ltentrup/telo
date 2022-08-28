use crate::{
    automaton::{DeterministicSafetyAutomaton, StateId},
    Domain, Predicates,
};

struct Monitor<D: Domain> {
    predicates: Predicates<D>,
    automaton: DeterministicSafetyAutomaton,
    state: StateId,
}

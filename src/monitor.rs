use crate::{
    automaton::{DeterministicSafetyAutomaton, StateId},
    Domain, Predicates,
};

struct Monitor<D: Domain> {
    predicates: Predicates<D>,
    automaton: DeterministicSafetyAutomaton,
    state: StateId,
}

impl<D: Domain> Monitor<D> {
    fn new(predicates: Predicates<D>, automaton: DeterministicSafetyAutomaton) -> Self {
        let initial_state = automaton.get_initial();
        Self {
            predicates,
            automaton,
            state: initial_state,
        }
    }

    fn next_state(&mut self, observation: &D) -> bool {
        let valuation = self.predicates.evaluate(observation);
        match self.automaton.next_state(self.state, &valuation) {
            Some(state) => {
                self.state = state;
                true
            }
            None => false,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{tests::TestObs, ClosurePredicate, PredicateId, Predicates};

    #[test]
    fn invariant() {
        let predicates = crate::tests::predicates();
        let eq_a = PredicateId(0);

        let var = predicates.bdd_variable(eq_a);
        let bdd = predicates.bdd_manager().mk_literal(*var, true);

        let automaton =
            DeterministicSafetyAutomaton::new_invariant(predicates.bdd_manager().clone(), bdd);
        let initial = automaton.get_initial();

        let mut monitor = Monitor {
            predicates,
            automaton,
            state: initial,
        };

        assert!(monitor.next_state(&TestObs::A));
        assert!(monitor.next_state(&TestObs::A));
        assert!(monitor.next_state(&TestObs::A));
        assert!(!monitor.next_state(&TestObs::B));
    }
}

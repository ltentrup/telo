#![doc = include_str!("../README.md")]
#![deny(clippy::all)]
#![warn(clippy::pedantic, clippy::cargo)]
#![allow(clippy::module_name_repetitions)]

pub(crate) mod automaton;
pub mod monitor;
pub mod predicate;

use automaton::{
    Alternating, AlternatingBüchiAutomaton, AutomatonBuilder, Büchi, DeterministicSafetyAutomaton,
    StateId,
};
use biodivine_lib_bdd::Bdd;
use itertools::Itertools;
use maplit::hashset;
use predicate::{PredicateId, Predicates};
use std::collections::HashSet;

use crate::automaton::{NonDeterministicBüchiAutomaton, NonDeterministicSafetyAutomaton};

pub trait Domain: 'static {}

impl<T: 'static> Domain for T {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Property {
    // boolean
    True,
    Atomic(PredicateId),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),

    // temporal
    Always(Box<Self>),
    Finally(Box<Self>),
    Next(Box<Self>),
    Until(Box<Self>, Box<Self>),
    Release(Box<Self>, Box<Self>),
}

impl std::ops::BitAnd for Property {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}

impl std::ops::Not for Property {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.negate()
    }
}

impl Property {
    #[must_use]
    pub fn atomic(predicate: PredicateId) -> Self {
        Self::Atomic(predicate)
    }

    #[must_use]
    pub fn and(self, rhs: Self) -> Self {
        Self::And(self.into(), rhs.into())
    }

    #[must_use]
    pub fn negate(self) -> Self {
        Self::Not(self.into())
    }

    #[must_use]
    pub fn implies(self, conclusion: Self) -> Self {
        Self::Or((!self).into(), conclusion.into())
    }

    #[must_use]
    pub fn next(property: Self) -> Self {
        Self::Next(property.into())
    }

    #[must_use]
    pub fn always(property: Self) -> Self {
        Self::Always(property.into())
    }

    /// Shorthand for `always not P`
    #[must_use]
    pub fn never(property: Self) -> Self {
        Self::Always(Self::Not(property.into()).into())
    }

    #[must_use]
    pub fn finally(property: Self) -> Self {
        Self::Finally(property.into())
    }

    #[must_use]
    pub fn until(self, rhs: Self) -> Self {
        Self::Until(self.into(), rhs.into())
    }

    #[must_use]
    pub fn release(self, rhs: Self) -> Self {
        Self::Release(self.into(), rhs.into())
    }

    /// Translates the temporal property into a deterministic safety automaton
    /// that is suitable for runtime verification, i.e., monitoring.
    #[must_use]
    pub fn to_monitoring_automaton<D: Domain>(
        &self,
        predicates: &Predicates<D>,
    ) -> DeterministicSafetyAutomaton {
        let nnf = self.to_nnf();

        let büchi = nnf.to_alternating_büchi(predicates);
        let büchi = NonDeterministicBüchiAutomaton::from(&büchi);
        let safety = NonDeterministicSafetyAutomaton::from(&büchi);

        safety.determinize().minimize()
    }

    /// Returns true when the formula is in negation normal form.
    #[must_use]
    pub fn is_in_nnf(&self) -> bool {
        match self {
            Self::True | Self::Atomic(_) => true,
            Self::Not(subf) => matches!(subf.as_ref(), Self::True | Self::Atomic(_)),
            Self::And(lhs, rhs)
            | Self::Or(lhs, rhs)
            | Self::Until(lhs, rhs)
            | Self::Release(lhs, rhs) => lhs.is_in_nnf() && rhs.is_in_nnf(),
            Self::Always(subf) | Self::Finally(subf) | Self::Next(subf) => subf.is_in_nnf(),
        }
    }

    /// Returns a new formula that accepts the same language and is in
    /// negation normal form. The size of the new formula is at most
    /// 2 times larger than the original formula.
    #[must_use]
    pub fn to_nnf(&self) -> Property {
        self.to_nnf_core(false)
    }

    fn to_nnf_core(&self, negated: bool) -> Self {
        match self {
            Self::True => {
                if negated {
                    Self::Not(Self::True.into())
                } else {
                    Self::True
                }
            }
            Self::Atomic(_) => {
                if negated {
                    Self::Not(self.clone().into())
                } else {
                    self.clone()
                }
            }
            Self::Not(subf) => subf.to_nnf_core(!negated),
            Self::And(lhs, rhs) => {
                let lhs = lhs.to_nnf_core(negated);
                let rhs = rhs.to_nnf_core(negated);
                if negated {
                    Self::Or(lhs.into(), rhs.into())
                } else {
                    Self::And(lhs.into(), rhs.into())
                }
            }
            Self::Or(lhs, rhs) => {
                let lhs = lhs.to_nnf_core(negated);
                let rhs = rhs.to_nnf_core(negated);
                if negated {
                    Self::And(lhs.into(), rhs.into())
                } else {
                    Self::Or(lhs.into(), rhs.into())
                }
            }
            Self::Always(subf) => {
                let subf = subf.to_nnf_core(negated);
                if negated {
                    Self::Finally(subf.into())
                } else {
                    Self::Always(subf.into())
                }
            }
            Self::Finally(subf) => {
                let subf = subf.to_nnf_core(negated);
                if negated {
                    Self::Always(subf.into())
                } else {
                    Self::Finally(subf.into())
                }
            }
            Self::Next(subf) => {
                let subf = subf.to_nnf_core(negated);
                Self::Next(subf.into())
            }
            Self::Until(lhs, rhs) => {
                let lhs = lhs.to_nnf_core(negated);
                let rhs = rhs.to_nnf_core(negated);
                if negated {
                    Self::Release(lhs.into(), rhs.into())
                } else {
                    Self::Until(lhs.into(), rhs.into())
                }
            }
            Self::Release(lhs, rhs) => {
                let lhs = lhs.to_nnf_core(negated);
                let rhs = rhs.to_nnf_core(negated);
                if negated {
                    Self::Until(lhs.into(), rhs.into())
                } else {
                    Self::Release(lhs.into(), rhs.into())
                }
            }
        }
    }

    fn format<D: Domain>(&self, predicates: &Predicates<D>) -> String {
        match self {
            Self::True => "true".to_string(),
            Self::Atomic(expr) => format!("({})", predicates[*expr]),
            Self::Not(subf) => format!("!{}", subf.format(predicates)),
            Self::And(lhs, rhs) => {
                format!("({} & {})", lhs.format(predicates), rhs.format(predicates))
            }
            Self::Or(lhs, rhs) => {
                format!("({} | {})", lhs.format(predicates), rhs.format(predicates))
            }
            Self::Always(subf) => format!("G {}", subf.format(predicates)),
            Self::Finally(subf) => format!("F {}", subf.format(predicates)),
            Self::Next(subf) => format!("X {}", subf.format(predicates)),
            Self::Until(lhs, rhs) => {
                format!("({} U {})", lhs.format(predicates), rhs.format(predicates))
            }
            Self::Release(lhs, rhs) => {
                format!("({} R {})", lhs.format(predicates), rhs.format(predicates))
            }
        }
    }

    fn to_alternating_büchi<D: Domain>(
        &self,
        predicates: &Predicates<D>,
    ) -> AlternatingBüchiAutomaton {
        assert!(self.is_in_nnf());
        let mut automaton = AlternatingBüchiAutomaton::builder(predicates.bdd_manager());
        let accepting_sink = automaton.new_state(Some("true"));
        automaton.add_edge(
            accepting_sink,
            predicates.bdd_manager().mk_true(),
            hashset! { accepting_sink },
        );
        let initial_state =
            self.to_alternating_büchi_state(predicates, &mut automaton, accepting_sink);
        automaton.set_initial(initial_state);
        automaton
            .build()
            .expect("construction of alternating automata should not fail")
    }

    fn to_alternating_büchi_state<D: Domain>(
        &self,
        predicates: &Predicates<D>,
        automaton: &mut AutomatonBuilder<Alternating, Büchi>,
        accepting_sink: StateId,
    ) -> StateId {
        if let Self::True = self {
            return accepting_sink;
        }
        let state = automaton.new_state(Some(&self.format(predicates)));
        let set = predicates.bdd_manager();

        match self {
            Self::True => unreachable!("this case is handled before"),
            Self::Atomic(predicate) => {
                automaton.add_edge(
                    state,
                    set.mk_literal(predicates.bdd_variable(*predicate), true),
                    hashset! {accepting_sink},
                );
            }
            Self::Not(subf) => match subf.as_ref() {
                Self::Atomic(predicate) => {
                    automaton.add_edge(
                        state,
                        set.mk_literal(predicates.bdd_variable(*predicate), false),
                        hashset! {accepting_sink},
                    );
                }
                Self::True => {
                    // the `false` state has no outgoing edges
                }
                _ => unreachable!("formula is in negation normal form"),
            },
            Self::And(lhs, rhs) => {
                let lhs = lhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                let rhs = rhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                for ((left_guard, left_target), (right_guard, right_target)) in
                    lhs.iter().cartesian_product(&rhs)
                {
                    let guard = left_guard.and(right_guard);
                    let target = left_target.iter().chain(right_target).copied().collect();
                    automaton.add_edge(state, guard, target);
                }
            }
            Self::Or(lhs, rhs) => {
                let lhs = lhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                let rhs = rhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                for (guard, target) in lhs.iter().chain(&rhs) {
                    automaton.add_edge(state, guard.clone(), target.clone());
                }
            }
            Self::Always(subf) => {
                let edges = subf.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                for (guard, mut target) in edges {
                    // since the constraint is conjunctive, we can remove edges to the accepting sink
                    target.retain(|&s| s != accepting_sink);
                    target.insert(state);
                    automaton.add_edge(state, guard, target);
                }
                automaton.add_accepting(state);
            }
            Self::Finally(subf) => {
                let edges = subf.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                for (guard, target) in edges {
                    automaton.add_edge(state, guard, target);
                }
                automaton.add_edge(state, set.mk_true(), hashset! {state});
            }
            Self::Next(subf) => {
                let next_state =
                    subf.to_alternating_büchi_state(predicates, automaton, accepting_sink);
                automaton.add_edge(state, set.mk_true(), hashset! {next_state});
            }
            Self::Until(lhs, rhs) => {
                let lhs = lhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                let rhs = rhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                for (guard, target) in rhs {
                    automaton.add_edge(state, guard, target);
                }
                for (guard, mut target) in lhs {
                    // since the constraint is conjunctive, we can remove edges to the accepting sink
                    target.retain(|&s| s != accepting_sink);
                    target.insert(state);
                    automaton.add_edge(state, guard, target);
                }
            }
            Self::Release(lhs, rhs) => {
                let lhs = lhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                let rhs = rhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                for ((left_guard, left_target), (right_guard, right_target)) in
                    lhs.iter().cartesian_product(&rhs)
                {
                    let guard = left_guard.and(right_guard);
                    let target = left_target.iter().chain(right_target).copied().collect();
                    automaton.add_edge(state, guard, target);
                }
                for (guard, mut target) in rhs {
                    // since the constraint is conjunctive, we can remove edges to the accepting sink
                    target.retain(|&s| s != accepting_sink);
                    target.insert(state);
                    automaton.add_edge(state, guard, target);
                }
                automaton.add_accepting(state);
            }
        }

        state
    }

    fn to_alternating_büchi_edge<D: Domain>(
        &self,
        predicates: &Predicates<D>,
        automaton: &mut AutomatonBuilder<Alternating, Büchi>,
        accepting_sink: StateId,
    ) -> Vec<(Bdd, HashSet<StateId>)> {
        match self {
            Self::True => {
                vec![(
                    predicates.bdd_manager().mk_true(),
                    hashset! {accepting_sink},
                )]
            }
            Self::Atomic(predictate) => {
                vec![(
                    predicates
                        .bdd_manager()
                        .mk_literal(predicates.bdd_variable(*predictate), true),
                    hashset! {accepting_sink},
                )]
            }
            Self::Not(subf) => match subf.as_ref() {
                Self::Atomic(predicate) => {
                    vec![(
                        predicates
                            .bdd_manager()
                            .mk_literal(predicates.bdd_variable(*predicate), false),
                        hashset! {accepting_sink},
                    )]
                }
                Self::True => {
                    vec![(predicates.bdd_manager().mk_false(), HashSet::default())]
                }
                _ => unreachable!("formula is in negation normal form"),
            },
            Self::And(lhs, rhs) => {
                let lhs = lhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                let rhs = rhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                lhs.iter()
                    .cartesian_product(&rhs)
                    .map(|((left_guard, left_target), (right_guard, right_target))| {
                        let guard = left_guard.and(right_guard);
                        let target = left_target.iter().chain(right_target).copied().collect();
                        (guard, target)
                    })
                    .collect()
            }
            Self::Or(lhs, rhs) => {
                let mut lhs = lhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                let mut rhs = rhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                lhs.append(&mut rhs);
                lhs
            }
            Self::Always(subf) => {
                let state = self.to_alternating_büchi_state(predicates, automaton, accepting_sink);
                let res = subf.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                res.into_iter()
                    .map(|(guard, mut target)| {
                        target.insert(state);
                        (guard, target)
                    })
                    .collect()
            }
            Self::Finally(subf) => {
                let state = self.to_alternating_büchi_state(predicates, automaton, accepting_sink);
                let mut res =
                    subf.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                res.push((predicates.bdd_manager().mk_true(), hashset! {state}));
                res
            }
            Self::Next(subf) => {
                let state = subf.to_alternating_büchi_state(predicates, automaton, accepting_sink);
                vec![(predicates.bdd_manager().mk_true(), hashset! {state})]
            }
            Property::Until(lhs, rhs) => {
                let state = self.to_alternating_büchi_state(predicates, automaton, accepting_sink);
                let lhs = lhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                let mut rhs = rhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                rhs.extend(lhs.into_iter().map(|(guard, mut target)| {
                    target.insert(state);
                    (guard, target)
                }));
                rhs
            }
            Property::Release(lhs, rhs) => {
                let state = self.to_alternating_büchi_state(predicates, automaton, accepting_sink);
                let lhs = lhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                let rhs = rhs.to_alternating_büchi_edge(predicates, automaton, accepting_sink);
                rhs.iter()
                    .cloned()
                    .map(|(guard, mut target)| {
                        target.insert(state);
                        (guard, target)
                    })
                    .chain(lhs.iter().cartesian_product(&rhs).map(
                        |((left_guard, left_target), (right_guard, right_target))| {
                            let guard = left_guard.and(right_guard);
                            let target = left_target.iter().chain(right_target).copied().collect();
                            (guard, target)
                        },
                    ))
                    .collect()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate::ClosurePredicate;

    #[derive(Debug, PartialEq, Eq)]
    pub(crate) enum TestObs {
        A,
        B,
    }

    pub(crate) fn predicates() -> Predicates<TestObs> {
        let mut builder = Predicates::builder();
        let _ = builder.new_predicate(ClosurePredicate {
            name: "obs is equal to A",
            closure: Box::new(|p: &TestObs| *p == TestObs::A),
        });
        let _ = builder.new_predicate(ClosurePredicate {
            name: "obs is equal to B",
            closure: Box::new(|p| *p == TestObs::B),
        });
        builder.build()
    }

    #[test]
    fn simple() {
        let predicates = predicates();
        let eq_a = PredicateId::new_unchecked(0);
        let eq_b = PredicateId::new_unchecked(1);

        let prop = Property::always(
            Property::atomic(eq_b).implies(Property::next(Property::never(Property::atomic(eq_a)))),
        );

        let safety = prop.to_monitoring_automaton(&predicates);
        assert_eq!(safety.state_count(), 2);

        // build the reference automaton
        let mut reference = DeterministicSafetyAutomaton::builder(predicates.bdd_manager());
        let state_1 = reference.new_state(Some("wait_for_b"));
        let state_2 = reference.new_state(Some("never_a"));
        let a = predicates.bdd_variable(eq_a);
        let b = predicates.bdd_variable(eq_b);
        let reference = reference
            .set_initial(state_1)
            .add_edge(
                state_1,
                &predicates.bdd_manager().mk_literal(b, false),
                state_1,
            )
            .add_edge(
                state_1,
                &predicates.bdd_manager().mk_literal(b, true),
                state_2,
            )
            .add_edge(
                state_2,
                &predicates.bdd_manager().mk_literal(a, false),
                state_2,
            )
            .build()
            .unwrap();

        assert!(safety.is_equivalent_to(&reference));
    }

    #[test]
    fn always_below_and() {
        let predicates = predicates();
        let eq_a = PredicateId::new_unchecked(0);
        let eq_b = PredicateId::new_unchecked(1);

        let prop = Property::atomic(eq_b).and(Property::always(Property::atomic(eq_a)));

        let safety = prop.to_monitoring_automaton(&predicates);

        // build the reference automaton
        let mut reference = DeterministicSafetyAutomaton::builder(predicates.bdd_manager());
        let state_1 = reference.new_state(Some("b && G a"));
        let state_2 = reference.new_state(Some("G a"));
        let a = predicates.bdd_variable(eq_a);
        let b = predicates.bdd_variable(eq_b);
        let reference = reference
            .set_initial(state_1)
            .add_edge(
                state_1,
                &predicates
                    .bdd_manager()
                    .mk_literal(a, true)
                    .and(&predicates.bdd_manager().mk_literal(b, true)),
                state_2,
            )
            .add_edge(
                state_2,
                &predicates.bdd_manager().mk_literal(a, true),
                state_2,
            )
            .build()
            .unwrap();

        assert!(safety.is_equivalent_to(&reference));
    }

    #[test]
    fn test_release() {
        let predicates = predicates();
        let eq_a = PredicateId::new_unchecked(0);
        let eq_b = PredicateId::new_unchecked(1);

        let prop = Property::release(Property::atomic(eq_a), Property::atomic(eq_b));

        let safety = prop.to_monitoring_automaton(&predicates);

        // build the reference automaton
        let mut reference = DeterministicSafetyAutomaton::builder(predicates.bdd_manager());
        let state_1 = reference.new_state(Some("a R b"));
        let state_2 = reference.new_state(Some("true"));
        let a = predicates.bdd_variable(eq_a);
        let b = predicates.bdd_variable(eq_b);
        let reference = reference
            .set_initial(state_1)
            .add_edge(
                state_1,
                &predicates
                    .bdd_manager()
                    .mk_literal(a, false)
                    .and(&predicates.bdd_manager().mk_literal(b, true)),
                state_1,
            )
            .add_edge(
                state_1,
                &predicates
                    .bdd_manager()
                    .mk_literal(a, true)
                    .and(&predicates.bdd_manager().mk_literal(b, true)),
                state_2,
            )
            .add_edge(state_2, &predicates.bdd_manager().mk_true(), state_2)
            .build()
            .unwrap();

        assert!(safety.is_equivalent_to(&reference));
    }

    #[test]
    fn test_true() {
        let predicates = predicates();

        let prop = Property::True;

        let safety = prop.to_monitoring_automaton(&predicates);
        assert_eq!(safety.state_count(), 1);

        // build the reference automaton
        let mut reference = DeterministicSafetyAutomaton::builder(predicates.bdd_manager());
        let state_1 = reference.new_state(Some("true"));
        let reference = reference
            .set_initial(state_1)
            .add_edge(state_1, &predicates.bdd_manager().mk_true(), state_1)
            .build()
            .unwrap();

        assert!(safety.is_equivalent_to(&reference));
    }

    #[test]
    fn test_false() {
        let predicates = predicates();

        let prop = Property::Not(Property::True.into());

        let safety = prop.to_monitoring_automaton(&predicates);
        assert_eq!(safety.state_count(), 1);

        // build the reference automaton
        let mut reference = DeterministicSafetyAutomaton::builder(predicates.bdd_manager());
        let state_1 = reference.new_state(Some("true"));
        let reference = reference.set_initial(state_1).build().unwrap();

        assert!(safety.is_equivalent_to(&reference));
    }

    #[test]
    fn negation_normal_form() {
        let eq_a = PredicateId::new_unchecked(0);
        let eq_b = PredicateId::new_unchecked(1);

        let prop = Property::until(Property::atomic(eq_a), Property::atomic(eq_b)).negate();
        let prop_nnf = Property::release(
            Property::atomic(eq_a).negate(),
            Property::atomic(eq_b).negate(),
        );
        assert_eq!(prop.to_nnf(), prop_nnf);
    }
}

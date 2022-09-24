//! Alternating automaton

use biodivine_lib_bdd::{Bdd, BddValuation, BddVariableSet};
use bitvec::vec::BitVec;
use itertools::Itertools;
use maplit::hashmap;
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
};
use thiserror::Error;

mod dot;

#[derive(Error, Debug)]
pub enum Error {
    #[error("missing initial state, call `set_initial` before `build`")]
    MissingInitialState,
}

#[derive(Clone)]
pub struct Automaton<Edg, Acc> {
    initial_state: StateId,
    states: Vec<State>,
    transitions: Vec<Edg>,
    acceptance: Acc,
    variables: BddVariableSet,
}

#[derive(Clone)]
pub struct AutomatonBuilder<Edg, Acc> {
    initial_state: Option<StateId>,
    states: Vec<State>,
    transitions: Vec<Edg>,
    acceptance: Acc,
    variables: BddVariableSet,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct Alternating(Vec<(Bdd, HashSet<StateId>)>);

#[derive(Debug, Clone, Default)]
pub(crate) struct NonDeterministic(HashMap<StateId, Bdd>);

#[derive(Debug, Clone, Default)]
pub struct Deterministic(HashMap<StateId, Bdd>);

/// Runs that visit the provided states infinitely often are accepting.
#[derive(Debug, Clone, Default)]
pub(crate) struct Büchi(Vec<StateId>);

/// All runs of an automaton are accepting.
#[derive(Debug, Clone, Copy, Default)]
pub struct Safety(());

pub(crate) type AlternatingBüchiAutomaton = Automaton<Alternating, Büchi>;
pub(crate) type NonDeterministicBüchiAutomaton = Automaton<NonDeterministic, Büchi>;
pub(crate) type NonDeterministicSafetyAutomaton = Automaton<NonDeterministic, Safety>;
pub type DeterministicSafetyAutomaton = Automaton<Deterministic, Safety>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StateId(usize);

#[derive(Debug, Clone)]
struct State {
    id: StateId,
    name: Option<String>,
}

impl<Edg, Acc: Default> Automaton<Edg, Acc> {
    pub fn builder(variables: &BddVariableSet) -> AutomatonBuilder<Edg, Acc> {
        AutomatonBuilder {
            initial_state: None,
            states: Vec::new(),
            transitions: Vec::new(),
            acceptance: Acc::default(),
            variables: variables.clone(),
        }
    }
}

impl<Edg: Clone + Default, Acc: Clone> AutomatonBuilder<Edg, Acc> {
    pub fn set_initial(&mut self, state: StateId) -> &mut Self {
        self.initial_state = Some(state);
        self
    }

    pub fn new_state(&mut self, name: Option<&str>) -> StateId {
        let id = StateId(self.states.len());
        self.states.push(State {
            id,
            name: name.map(str::to_string),
        });
        self.transitions.push(Edg::default());
        assert_eq!(self.states.len(), self.transitions.len());

        id
    }

    pub fn build(&self) -> Result<Automaton<Edg, Acc>, Error> {
        Ok(Automaton {
            initial_state: self.initial_state.ok_or(Error::MissingInitialState)?,
            states: self.states.clone(),
            transitions: self.transitions.clone(),
            acceptance: self.acceptance.clone(),
            variables: self.variables.clone(),
        })
    }
}

impl<Edg, Acc> Automaton<Edg, Acc> {
    pub(crate) fn state_count(&self) -> usize {
        self.states.len()
    }

    pub(crate) fn get_initial(&self) -> StateId {
        self.initial_state
    }
}

impl<Acc> AutomatonBuilder<NonDeterministic, Acc> {
    pub(crate) fn add_edge(&mut self, state: StateId, guard: &Bdd, target: StateId) -> &mut Self {
        if guard.is_false() {
            return self;
        }
        let entry = self.transitions[state.0]
            .0
            .entry(target)
            .or_insert_with(|| self.variables.mk_false());
        *entry = entry.or(guard);
        self
    }
}

impl<Acc> AutomatonBuilder<Alternating, Acc> {
    pub(crate) fn add_edge(
        &mut self,
        state: StateId,
        guard: Bdd,
        target: HashSet<StateId>,
    ) -> &mut Self {
        if guard.is_false() {
            return self;
        }
        // check if there is an existing edge with the same target
        for (other_guard, other_target) in &mut self.transitions[state.0].0 {
            if target == *other_target {
                *other_guard = other_guard.or(&guard);
                return self;
            }
        }
        self.transitions[state.0].0.push((guard, target));
        self
    }
}

impl<Acc> AutomatonBuilder<Deterministic, Acc> {
    pub(crate) fn add_edge(&mut self, state: StateId, guard: &Bdd, target: StateId) -> &mut Self {
        if guard.is_false() {
            return self;
        }
        // check that transition guards are non-overlapping
        for (other_target, other_guard) in &self.transitions[state.0].0 {
            if target == *other_target && guard == other_guard {
                return self;
            }
            assert!(
                guard.and(other_guard).is_false(),
                "Overlapping guards are not allowed for deterministic automata",
            );
        }

        let entry = self.transitions[state.0]
            .0
            .entry(target)
            .or_insert_with(|| self.variables.mk_false());
        *entry = entry.or(guard);
        self
    }
}

impl<Acc> Automaton<Deterministic, Acc> {
    pub(crate) fn next_state(&self, state: StateId, valuation: &BddValuation) -> Option<StateId> {
        self.transitions[state.0]
            .0
            .iter()
            .find(|(_, guard)| guard.eval_in(valuation))
            .map(|(target, _)| *target)
    }
}

impl<Edg> AutomatonBuilder<Edg, Büchi> {
    pub(crate) fn add_accepting(&mut self, state: StateId) {
        self.acceptance.0.push(state);
    }
}

impl NonDeterministicBüchiAutomaton {
    /// Constructs a non-deterministic automaton that accepts the same
    /// language as the provided alternating automaton.
    ///
    /// The conversion is implemented using the Miyano-Hayashi construction.
    pub(crate) fn from(alternating: &AlternatingBüchiAutomaton) -> Self {
        let variables = &alternating.variables;
        let mut automaton = NonDeterministicBüchiAutomaton::builder(variables);
        let initial_state = (
            PowerState::singleton(alternating, alternating.initial_state),
            PowerState::empty(alternating),
        );
        let formatted = format_state(&initial_state);
        let initial_state_id = automaton.new_state(Some(&formatted));
        let mut mapping = hashmap! {initial_state.clone() => initial_state_id};
        automaton.set_initial(initial_state_id);
        automaton.add_accepting(initial_state_id);

        let accepting_states = PowerState::from(alternating, &alternating.acceptance.0);
        let mut queue = VecDeque::from([initial_state]);

        while let Some(state) = queue.pop_front() {
            for (guard, (left, right)) in state
                .0
                .iter()
                .map(|s| {
                    alternating.transitions[s.0]
                        .0
                        .iter()
                        .zip(std::iter::repeat(state.1.contains(s)))
                })
                .multi_cartesian_product()
                .map(|edges| {
                    edges.iter().fold(
                        (
                            variables.mk_true(),
                            (
                                PowerState::empty(alternating),
                                PowerState::empty(alternating),
                            ),
                        ),
                        |(val_guard, (mut left, mut right)), ((guard, targets), accepting)| {
                            for target in targets {
                                left.add(*target);
                                if *accepting {
                                    right.add(*target);
                                }
                            }
                            (val_guard.and(guard), (left, right))
                        },
                    )
                })
            {
                let accepting_states = if state.1.is_empty() {
                    left.without(&accepting_states)
                } else {
                    right.without(&accepting_states)
                };
                let target_states = (left, accepting_states);
                let formatted = format_state(&target_states);
                let target = *mapping.entry(target_states.clone()).or_insert_with(|| {
                    let id = automaton.new_state(Some(&formatted));
                    if target_states.1.is_empty() {
                        automaton.add_accepting(id);
                    }
                    queue.push_back(target_states);
                    id
                });
                automaton.add_edge(mapping[&state], &guard, target);
            }
        }

        automaton
            .build()
            .expect("automaton construction should not fail")
    }
}

fn format_state((left, right): &(PowerState, PowerState)) -> String {
    format!("({}, {})", left, right)
}

fn format_bdd(bdd: &Bdd, variables: &BddVariableSet) -> String {
    if bdd.is_true() {
        return "true".to_string();
    } else if bdd.is_false() {
        return "false".to_string();
    }
    let dnf = bdd
        .sat_clauses()
        .map(|clause| {
            clause
                .to_values()
                .into_iter()
                .map(|(var, val)| {
                    format!("{}({})", if val { "" } else { "!" }, variables.name_of(var))
                })
                .collect::<Vec<_>>()
                .join(" & ")
        })
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(!dnf.is_empty());
    dnf
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct PowerState(BitVec);

impl PowerState {
    fn empty<Edg, Acc>(automaton: &Automaton<Edg, Acc>) -> Self {
        Self(BitVec::repeat(false, automaton.states.len()))
    }

    fn is_empty(&self) -> bool {
        self.0.not_any()
    }

    fn all<Edg, Acc>(automaton: &Automaton<Edg, Acc>) -> Self {
        Self(BitVec::repeat(true, automaton.states.len()))
    }

    fn singleton<Edg, Acc>(automaton: &Automaton<Edg, Acc>, state: StateId) -> Self {
        let mut bitvec = BitVec::repeat(false, automaton.states.len());
        bitvec.set(state.0, true);
        Self(bitvec)
    }

    fn from<Edg, Acc>(automaton: &Automaton<Edg, Acc>, states: &[StateId]) -> Self {
        let mut bitvec = BitVec::repeat(false, automaton.states.len());
        for state in states {
            bitvec.set(state.0, true);
        }
        Self(bitvec)
    }

    fn iter(&self) -> impl Iterator<Item = StateId> + '_ + Clone {
        self.0
            .iter()
            .enumerate()
            .filter(|(_, val)| **val)
            .map(|(idx, _)| StateId(idx))
    }

    fn without(&self, other: &Self) -> PowerState {
        PowerState(self.0.clone() & &!other.0.clone())
    }

    fn contains(&self, state: StateId) -> bool {
        self.0[state.0]
    }

    fn add(&mut self, state: StateId) {
        self.0.set(state.0, true);
    }
}

impl std::fmt::Display for PowerState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?}",
            self.0
                .iter()
                .enumerate()
                .filter(|(_, val)| **val)
                .map(|(idx, _)| idx)
                .collect::<Vec<_>>(),
        )
    }
}

impl NonDeterministicSafetyAutomaton {
    /// Interpret a Büchi automaton as a safety automaton, thus, ignoring
    /// the Büchi acceptance condition. All runs in the resulting automaton
    /// are accepting.
    pub(crate) fn from(automaton: &NonDeterministicBüchiAutomaton) -> Self {
        Self {
            initial_state: automaton.initial_state,
            states: automaton.states.clone(),
            transitions: automaton.transitions.clone(),
            acceptance: Safety(()),
            variables: automaton.variables.clone(),
        }
    }

    /// Checks whether the automaton is deterministic, i.e., for every state
    /// and every pair of outgoing transition of this state, the transition
    /// guards are non-overlapping.
    pub fn is_deterministic(&self) -> bool {
        self.states.iter().all(|state| {
            self.transitions[state.id.0]
                .0
                .iter()
                .tuple_combinations()
                .all(|((target, guard), (other_target, other_guard))| {
                    assert!(target != other_target);
                    guard.and(other_guard).is_false()
                })
        })
    }

    /// Creates a new deterministic automaton that accepts the same language.
    pub(crate) fn determinize(&self) -> DeterministicSafetyAutomaton {
        let initial_state = PowerState::singleton(self, self.initial_state);
        let formatted = format!("{initial_state}");
        let mut automaton = DeterministicSafetyAutomaton::builder(&self.variables);
        // DeterministicSafetyAutomaton::new_with_state(&self.variables, );
        let initial_state_id = automaton.new_state(Some(&formatted));
        automaton.set_initial(initial_state_id);
        let mut mapping = hashmap! {initial_state.clone() => initial_state_id};

        let mut queue = VecDeque::from([initial_state]);

        while let Some(state) = queue.pop_front() {
            // collect all possible transitions
            let transitions: Vec<_> = state
                .iter()
                .flat_map(|s| {
                    self.transitions[s.0]
                        .0
                        .iter()
                        .map(|(target, guard)| (guard.clone(), *target))
                })
                .collect();
            for x in (0..transitions.len()).powerset().skip(1) {
                let (guard, targets) = transitions.iter().enumerate().fold(
                    (automaton.variables.mk_true(), Vec::new()),
                    |(val_guard, mut val_target), (idx, (guard, target))| {
                        if x.contains(&idx) {
                            val_target.push(*target);
                            (val_guard.and(guard), val_target)
                        } else {
                            (val_guard.and(&guard.not()), val_target)
                        }
                    },
                );
                if guard.is_false() {
                    continue;
                }
                let targets = PowerState::from(self, &targets);
                let formatted = format!("{targets}");
                let target = *mapping.entry(targets.clone()).or_insert_with(|| {
                    let id = automaton.new_state(Some(&formatted));
                    queue.push_back(targets);
                    id
                });
                automaton.add_edge(mapping[&state], &guard, target);
            }
        }
        automaton.build().expect("determinization should not fail")
    }
}

impl DeterministicSafetyAutomaton {
    #[cfg(test)]
    pub(crate) fn new_invariant(variables: BddVariableSet, invariant: Bdd) -> Self {
        Self {
            initial_state: StateId(0),
            states: vec![State {
                id: StateId(0),
                name: None,
            }],
            transitions: vec![Deterministic(hashmap! {StateId(0) => invariant})],
            acceptance: Safety(()),
            variables,
        }
    }

    /// Minimizes the number of states of a deterministic automaton.
    pub(crate) fn minimize(&self) -> Self {
        let equivalence_classes = self.determine_equivalence_classes();

        // build the automaton from the equivalence classes
        let initial_state = equivalence_classes
            .iter()
            .find(|class| class.contains(self.initial_state))
            .expect("every state is in exactly one equivalence class");
        let mut automaton = Self::builder(&self.variables);
        let initial_state_id = automaton.new_state(Some(&format!("{initial_state}")));
        automaton.set_initial(initial_state_id);
        let mut mapping = hashmap! {initial_state.clone() => initial_state_id};

        for class in &equivalence_classes {
            let state_id = *mapping
                .entry(class.clone())
                .or_insert_with(|| automaton.new_state(Some(&format!("{class}"))));
            for state in class.iter() {
                for (target, guard) in &self.transitions[state.0].0 {
                    let target_class = equivalence_classes
                        .iter()
                        .find(|class| class.contains(*target))
                        .expect("every state is in exactly one equivalence class");
                    let target_state_id = *mapping
                        .entry(target_class.clone())
                        .or_insert_with(|| automaton.new_state(Some(&format!("{target_class}"))));
                    automaton.add_edge(state_id, guard, target_state_id);
                }
            }
        }
        automaton.build().expect("minimization should not fail")
    }

    fn determine_equivalence_classes(&self) -> Vec<PowerState> {
        // initially, all states start in the same equivalence class
        let mut equivalence_classes = vec![PowerState::all(self)];
        let mut new_equivalence_classes = Vec::new();
        loop {
            for class in &equivalence_classes {
                let pivot = class
                    .iter()
                    .next()
                    .expect("equivalence classes are not empty");
                let mut new_equiv = PowerState::singleton(self, pivot);
                let mut other_equiv = PowerState::empty(self);

                // compare every other state in the class with our pivot
                for other in class.iter().skip(1) {
                    let mut different = false;
                    let mut rejecting = self.variables.mk_true();
                    let mut other_rejecting = self.variables.mk_true();
                    for ((target, guard), (other_target, other_guard)) in self.transitions[pivot.0]
                        .0
                        .iter()
                        .cartesian_product(&self.transitions[other.0].0)
                    {
                        rejecting = rejecting.and(&guard.not());
                        other_rejecting = other_rejecting.and(&other_guard.not());
                        if guard.and(other_guard).is_false() {
                            continue;
                        }
                        let next_equiv = equivalence_classes
                            .iter()
                            .find(|class| class.contains(*target))
                            .expect("every state is in exactly one equivalence class");
                        if !next_equiv.contains(*other_target) {
                            different = true;
                        }
                    }
                    let one_has_no_transitions = self.transitions[pivot.0].0.is_empty()
                        ^ self.transitions[other.0].0.is_empty();
                    // If one state has no transitions, it holds that
                    // `rejecting == other_rejecting` as the loop above is not
                    // run. The states cannot be in the same equivalence class, though.
                    if one_has_no_transitions || rejecting != other_rejecting {
                        different = true;
                    }
                    if different {
                        other_equiv.add(other);
                    } else {
                        new_equiv.add(other);
                    }
                }

                new_equivalence_classes.push(new_equiv);
                if !other_equiv.is_empty() {
                    new_equivalence_classes.push(other_equiv);
                }
            }

            if equivalence_classes.len() == new_equivalence_classes.len() {
                break;
            }
            equivalence_classes = std::mem::take(&mut new_equivalence_classes);
        }
        equivalence_classes
    }

    fn concat(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.states.extend(other.states.iter().map(|s| State {
            id: StateId(s.id.0 + self.state_count()),
            name: s.name.clone(),
        }));
        result
            .transitions
            .extend(other.transitions.iter().map(|edge| {
                Deterministic(
                    edge.0
                        .iter()
                        .map(|(target, guard)| {
                            (StateId(target.0 + self.state_count()), guard.clone())
                        })
                        .collect(),
                )
            }));
        result
    }

    pub fn is_equivalent_to(&self, other: &Self) -> bool {
        let combined = self.concat(other);
        let left_initial = self.initial_state;
        let right_initial = StateId(other.initial_state.0 + self.state_count());
        let equivalences = combined.determine_equivalence_classes();
        equivalences.iter().any(|powerstate| {
            powerstate.contains(left_initial) && powerstate.contains(right_initial)
        })
    }
}

impl<'a> IntoIterator for &'a Deterministic {
    type Item = (&'a StateId, &'a Bdd);
    type IntoIter = std::collections::hash_map::Iter<'a, StateId, Bdd>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a NonDeterministic {
    type Item = (&'a StateId, &'a Bdd);
    type IntoIter = std::collections::hash_map::Iter<'a, StateId, Bdd>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl std::ops::Index<&StateId> for Deterministic {
    type Output = Bdd;

    fn index(&self, index: &StateId) -> &Self::Output {
        &self.0[index]
    }
}

impl std::ops::Index<&StateId> for NonDeterministic {
    type Output = Bdd;

    fn index(&self, index: &StateId) -> &Self::Output {
        &self.0[index]
    }
}

#[cfg(test)]
mod test {
    use super::DeterministicSafetyAutomaton;
    use biodivine_lib_bdd::{BddVariableSet, BddVariableSetBuilder};

    #[test]
    fn same_is_equivalent() {
        let mut builder = BddVariableSetBuilder::new();
        let [a, b] = builder.make(&["a", "b"]);
        let variables: BddVariableSet = builder.build();
        let invariant = variables
            .mk_literal(a, true)
            .and(&variables.mk_literal(b, false));
        let automaton = DeterministicSafetyAutomaton::new_invariant(variables.clone(), invariant);
        let copy = automaton.clone();
        assert!(automaton.is_equivalent_to(&copy));

        let invariant = variables
            .mk_literal(a, true)
            .and(&variables.mk_literal(b, true));
        let automaton2 = DeterministicSafetyAutomaton::new_invariant(variables, invariant);
        assert!(!automaton.is_equivalent_to(&automaton2));
    }
}

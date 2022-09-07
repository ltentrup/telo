//! Alternating automaton

use biodivine_lib_bdd::{Bdd, BddValuation, BddVariableSet};
use bitvec::vec::BitVec;
use itertools::Itertools;
use maplit::{hashmap, hashset};
use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
};

mod dot;

#[derive(Clone)]
pub(crate) struct Automaton<Edg, Acc> {
    initial_state: StateId,
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
pub(crate) struct Deterministic(HashMap<StateId, Bdd>);

/// Runs that visit the provided states infinitely often are accepting.
#[derive(Debug, Clone)]
pub(crate) struct Büchi(Vec<StateId>);

/// All runs of an automaton are accepting.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Safety(());

pub(crate) type AlternatingBüchiAutomaton = Automaton<Alternating, Büchi>;
pub(crate) type NonDeterministicBüchiAutomaton = Automaton<NonDeterministic, Büchi>;
pub(crate) type NonDeterministicSafetyAutomaton = Automaton<NonDeterministic, Safety>;
pub(crate) type DeterministicSafetyAutomaton = Automaton<Deterministic, Safety>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct StateId(usize);

#[derive(Debug, Clone)]
struct State {
    id: StateId,
    name: Option<String>,
}

impl<Edg: Default, Acc> Automaton<Edg, Acc> {
    pub(crate) fn new_state(&mut self, name: Option<&str>) -> StateId {
        let id = StateId(self.states.len());
        self.states.push(State {
            id,
            name: name.map(str::to_string),
        });
        self.transitions.push(Edg::default());
        assert_eq!(self.states.len(), self.transitions.len());

        id
    }

    pub(crate) fn set_initial(&mut self, state: StateId) {
        self.initial_state = state;
    }

    pub(crate) fn get_initial(&self) -> StateId {
        self.initial_state
    }
}

impl<Acc> Automaton<NonDeterministic, Acc> {
    pub(crate) fn add_edge(&mut self, state: StateId, guard: Bdd, target: StateId) {
        if guard.is_false() {
            return;
        }
        let entry = self.transitions[state.0]
            .0
            .entry(target)
            .or_insert_with(|| self.variables.mk_false());
        *entry = entry.or(&guard);
    }
}

impl<Acc> Automaton<Alternating, Acc> {
    pub(crate) fn add_edge(&mut self, state: StateId, guard: Bdd, target: HashSet<StateId>) {
        if guard.is_false() {
            return;
        }
        // check if there is an existing edge with the same target
        for (other_guard, other_target) in &mut self.transitions[state.0].0 {
            if target == *other_target {
                *other_guard = other_guard.or(&guard);
                return;
            }
        }
        self.transitions[state.0].0.push((guard, target));
    }
}

impl<Acc> Automaton<Deterministic, Acc> {
    pub(crate) fn add_edge(&mut self, state: StateId, guard: Bdd, target: StateId) {
        if guard.is_false() {
            return;
        }
        // check that transition guards are non-overlapping
        for (other_target, other_guard) in &self.transitions[state.0].0 {
            if target == *other_target && guard == *other_guard {
                return;
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
        *entry = entry.or(&guard);
    }

    pub(crate) fn next_state(&self, state: StateId, valuation: &BddValuation) -> Option<StateId> {
        self.transitions[state.0]
            .0
            .iter()
            .find(|(_, guard)| guard.eval_in(valuation))
            .map(|(target, _)| *target)
    }
}

impl<Edg> Automaton<Edg, Büchi> {
    pub(crate) fn add_accepting(&mut self, state: StateId) {
        self.acceptance.0.push(state);
    }
}

impl AlternatingBüchiAutomaton {
    pub(crate) fn new_büchi(variables: &BddVariableSet) -> Self {
        Self {
            initial_state: StateId(0),
            states: vec![State {
                id: StateId(0),
                name: Some("true".to_string()),
            }],
            transitions: vec![Alternating(vec![(
                variables.mk_true(),
                hashset! {StateId(0)},
            )])],
            acceptance: Büchi(vec![StateId(0)]),
            variables: variables.clone(),
        }
    }

    pub(crate) fn accepting_sink(&self) -> StateId {
        StateId(0)
    }
}

impl NonDeterministicBüchiAutomaton {
    fn new_büchi(variables: &BddVariableSet) -> Self {
        Self {
            initial_state: StateId(0),
            states: vec![State {
                id: StateId(0),
                name: Some("true".to_string()),
            }],
            transitions: vec![NonDeterministic(
                hashmap! {StateId(0) => variables.mk_true()},
            )],
            acceptance: Büchi(vec![StateId(0)]),
            variables: variables.clone(),
        }
    }
}

impl NonDeterministicBüchiAutomaton {
    /// Constructs a non-deterministic automaton that accepts the same
    /// language as the provided alternating automaton.
    ///
    /// The conversion is implemented using the Miyano-Hayashi construction.
    pub(crate) fn from(alternating: &AlternatingBüchiAutomaton) -> Self {
        let variables = &alternating.variables;
        let mut automaton = NonDeterministicBüchiAutomaton::new_büchi(variables);
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
            let formatted = format_state(&state);
            println!("{:?}", formatted);
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
                println!("  {} -> {formatted}", format_bdd(&guard, variables));
                let target = *mapping.entry(target_states.clone()).or_insert_with(|| {
                    let id = automaton.new_state(Some(&formatted));
                    if target_states.1.is_empty() {
                        automaton.add_accepting(id);
                    }
                    queue.push_back(target_states);
                    id
                });
                automaton.add_edge(mapping[&state], guard.clone(), target);
            }
        }

        automaton
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
    let mut dnf = bdd
        .sat_clauses()
        .map(|clause| {
            clause
                .to_values()
                .into_iter()
                .map(|(var, val)| {
                    format!(
                        "{}({})",
                        if !val { "!" } else { "" },
                        variables.name_of(var)
                    )
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

impl<Edg: Default> Automaton<Edg, Safety> {
    fn new_with_state(variables: &BddVariableSet, state: Option<&str>) -> Self {
        Self {
            initial_state: StateId(0),
            states: vec![State {
                id: StateId(0),
                name: state.map(|name| name.to_string()),
            }],
            transitions: vec![Edg::default()],
            acceptance: Safety(()),
            variables: variables.clone(),
        }
    }
}

impl NonDeterministicSafetyAutomaton {
    /// Returns an automaton that accepts all inputs.
    fn new(variables: &BddVariableSet) -> Self {
        Self {
            initial_state: StateId(0),
            states: vec![State {
                id: StateId(0),
                name: Some("true".to_string()),
            }],
            transitions: vec![NonDeterministic(
                hashmap! {StateId(0) => variables.mk_true()},
            )],
            acceptance: Safety(()),
            variables: variables.clone(),
        }
    }

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
    pub(crate) fn is_deterministic(&self) -> bool {
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
        let mut automaton =
            DeterministicSafetyAutomaton::new_with_state(&self.variables, Some(&formatted));
        let initial_state_id = automaton.initial_state;
        let mut mapping = hashmap! {initial_state.clone() => initial_state_id};

        let mut queue = VecDeque::from([initial_state]);

        while let Some(state) = queue.pop_front() {
            println!("{state}");
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
                        // println!(
                        //     "xxx {idx} {} {}",
                        //     format_bdd(&val_guard, &automaton.variables),
                        //     format_bdd(&guard, &automaton.variables)
                        // );
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
                println!(
                    "   -> {} {:?}",
                    format_bdd(&guard, &automaton.variables),
                    targets
                );
                let targets = PowerState::from(self, &targets);
                let formatted = format!("{targets}");
                let target = *mapping.entry(targets.clone()).or_insert_with(|| {
                    let id = automaton.new_state(Some(&formatted));
                    queue.push_back(targets);
                    id
                });
                automaton.add_edge(mapping[&state], guard.clone(), target);
            }
        }
        automaton
    }
}

impl DeterministicSafetyAutomaton {
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
                    assert!(!self.transitions[pivot.0].0.is_empty());
                    assert!(!self.transitions[other.0].0.is_empty());
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
                    if rejecting != other_rejecting {
                        different = true;
                    }
                    if different {
                        println!("different {:?} {:?}", pivot, other);
                        other_equiv.add(other);
                    } else {
                        println!("same {:?} {:?}", pivot, other);
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
            } else {
                equivalence_classes = std::mem::take(&mut new_equivalence_classes);
            }
        }

        // build the automaton from the equivalence classes
        let initial_state = equivalence_classes
            .iter()
            .find(|class| class.contains(self.initial_state))
            .expect("every state is in exactly one equivalence class");
        let mut automaton =
            Self::new_with_state(&self.variables, Some(&format!("{initial_state}")));
        let initial_state_id = automaton.initial_state;
        let mut mapping = hashmap! {initial_state.clone() => initial_state_id};

        for class in &equivalence_classes {
            println!("{class}");
            let state_id = *mapping
                .entry(class.clone())
                .or_insert_with(|| automaton.new_state(Some(&format!("{class}"))));
            for state in class.iter() {
                dbg!(&state);
                for (target, guard) in &self.transitions[state.0].0 {
                    let target_class = equivalence_classes
                        .iter()
                        .find(|class| class.contains(*target))
                        .expect("every state is in exactly one equivalence class");
                    let target_state_id = *mapping
                        .entry(target_class.clone())
                        .or_insert_with(|| automaton.new_state(Some(&format!("{target_class}"))));
                    automaton.add_edge(state_id, guard.clone(), target_state_id);
                }
            }
        }
        automaton
    }
}

impl<'a> IntoIterator for &'a Deterministic {
    type Item = (&'a StateId, &'a Bdd);
    type IntoIter = std::collections::hash_map::Iter<'a, StateId, Bdd>;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0).iter()
    }
}

impl<'a> IntoIterator for &'a NonDeterministic {
    type Item = (&'a StateId, &'a Bdd);
    type IntoIter = std::collections::hash_map::Iter<'a, StateId, Bdd>;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0).iter()
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

//! Alternating automaton

use super::{Domain, Proposition};
use crate::ExpressionProposition;
use bitvec::vec::BitVec;
use maplit::hashmap;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
    rc::Rc,
};

pub(crate) type AlternatingEdge<D> = Vec<(Rc<ExpressionProposition<D>>, Vec<StateId>)>;
pub(crate) type Edge<D> = Vec<(Rc<ExpressionProposition<D>>, StateId)>;

/// Representation of an alternating automaton.
#[derive(Clone)]
pub(crate) struct AlternatingAutomaton<D: Domain> {
    initial_state: StateId,
    states: Vec<State>,
    transitions: Vec<AlternatingEdge<D>>,
    acceptance: Acceptance,
}

#[derive(Clone)]
pub(crate) struct Automaton<D: Domain> {
    initial_state: StateId,
    states: Vec<State>,
    transitions: Vec<Edge<D>>,
    acceptance: Acceptance,
}

#[derive(Debug, Clone)]
pub(crate) enum Acceptance {
    Safety,
    Büchi(Vec<StateId>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct StateId(usize);

#[derive(Debug, Clone)]
struct State {
    id: StateId,
    name: Option<String>,
}

impl<D: Domain> AlternatingAutomaton<D> {
    pub(crate) fn new_büchi() -> Self {
        Self {
            initial_state: StateId(0),
            states: vec![State {
                id: StateId(0),
                name: Some("true".to_string()),
            }],
            transitions: vec![vec![(
                Rc::new(ExpressionProposition::make_true()),
                vec![StateId(0)],
            )]],
            acceptance: Acceptance::Büchi(vec![StateId(0)]),
        }
    }

    pub(crate) fn new_state(&mut self, name: Option<&str>) -> StateId {
        let id = StateId(self.states.len());
        self.states.push(State {
            id,
            name: name.map(str::to_string),
        });
        self.transitions.push(Vec::default());
        assert_eq!(self.states.len(), self.transitions.len());

        id
    }

    pub(crate) fn add_edge(
        &mut self,
        state: StateId,
        outgoing: (Rc<ExpressionProposition<D>>, Vec<StateId>),
    ) {
        self.transitions[state.0].push(outgoing);
    }

    pub(crate) fn accepting_sink(&self) -> StateId {
        StateId(0)
    }

    pub(crate) fn set_initial(&mut self, state: StateId) {
        self.initial_state = state;
    }

    pub(crate) fn add_accepting(&mut self, state: StateId) {
        match &mut self.acceptance {
            Acceptance::Safety => {}
            Acceptance::Büchi(states) => states.push(state),
        }
    }
}

impl<D: Domain> Automaton<D> {
    fn new_büchi() -> Self {
        Self {
            initial_state: StateId(0),
            states: vec![State {
                id: StateId(0),
                name: Some("true".to_string()),
            }],
            transitions: vec![vec![(
                Rc::new(ExpressionProposition::make_true()),
                StateId(0),
            )]],
            acceptance: Acceptance::Büchi(vec![StateId(0)]),
        }
    }

    pub(crate) fn new_state(&mut self, name: Option<&str>) -> StateId {
        let id = StateId(self.states.len());
        self.states.push(State {
            id,
            name: name.map(str::to_string),
        });
        self.transitions.push(Vec::default());
        assert_eq!(self.states.len(), self.transitions.len());

        id
    }

    pub(crate) fn add_edge(
        &mut self,
        state: StateId,
        guard: Rc<ExpressionProposition<D>>,
        target: StateId,
    ) {
        self.transitions[state.0].push((guard, target));
    }
}

impl<D: Domain> Automaton<D> {
    /// Constructs a non-deterministic automaton that accepts the same
    /// language as the provided alternating automaton.
    ///
    /// The conversion is implemented using the Miyano-Hayashi construction.
    pub(crate) fn from(alternating: &AlternatingAutomaton<D>) -> Self {
        let mut automaton = Automaton::new_büchi();
        let initial_state = (
            PowerState::singleton(alternating, alternating.initial_state),
            PowerState::empty(alternating),
        );
        let formatted = format_state(&initial_state);
        let mut mapping = hashmap! {initial_state.clone() => automaton.new_state(Some(&formatted))};
        let mut queue = VecDeque::from([initial_state]);

        while let Some(state) = queue.pop_front() {
            let formatted = format_state(&state);
            println!("{:?}", formatted);
            for s in state.0.iter() {
                for (guard, targets) in &alternating.transitions[s.0] {
                    println!("{guard}");
                    let target_states = PowerState::from(alternating, targets);
                    let target_states = (target_states, PowerState::empty(alternating));
                    let formatted = format_state(&target_states);
                    println!("{formatted}");
                    let entry = mapping.entry(target_states.clone()).or_insert_with(|| {
                        queue.push_back(target_states);
                        automaton.new_state(Some(&formatted))
                    });
                    automaton.add_edge(s, guard.clone(), *entry);
                }
            }

            todo!();
        }

        todo!();

        automaton
    }
}

fn format_state((left, right): &(PowerState, PowerState)) -> String {
    format!("({}, {})", left, right)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct PowerState(BitVec);

impl PowerState {
    fn empty<D: Domain>(alternating: &AlternatingAutomaton<D>) -> Self {
        Self(BitVec::repeat(false, alternating.states.len()))
    }

    fn all<D: Domain>(alternating: &AlternatingAutomaton<D>) -> Self {
        Self(BitVec::repeat(true, alternating.states.len()))
    }

    fn singleton<D: Domain>(alternating: &AlternatingAutomaton<D>, state: StateId) -> Self {
        let mut bitvec = BitVec::repeat(false, alternating.states.len());
        bitvec.set(state.0, true);
        Self(bitvec)
    }

    fn from<D: Domain>(alternating: &AlternatingAutomaton<D>, states: &[StateId]) -> Self {
        let mut bitvec = BitVec::repeat(false, alternating.states.len());
        for state in states {
            bitvec.set(state.0, true);
        }
        Self(bitvec)
    }

    fn iter(&self) -> impl Iterator<Item = StateId> + '_ {
        self.0
            .iter()
            .enumerate()
            .filter(|(_, val)| **val)
            .map(|(idx, _)| StateId(idx))
    }

    fn intersect(&mut self, other: &Self) {
        self.0 &= &other.0;
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

#[derive(Debug, Clone, Copy)]
pub(crate) enum AlternatingDrawNode {
    Node(StateId),
    /// A virtual node to represent AND transitions
    AndNode(StateId, usize),
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum AlternatingDrawEdge {
    NonDet(StateId, usize, StateId),
    ToAndNode(StateId, usize),
    FromAndNode(StateId, usize, StateId),
}

type Nd = AlternatingDrawNode;
type Ed = AlternatingDrawEdge;

impl<'a, D: Domain> dot::Labeller<'a, Nd, Ed> for AlternatingAutomaton<D> {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("alternating").unwrap()
    }

    fn node_id(&'a self, n: &Nd) -> dot::Id<'a> {
        match n {
            AlternatingDrawNode::Node(id) => dot::Id::new(format!("N{}", id.0)).unwrap(),
            AlternatingDrawNode::AndNode(id, idx) => {
                dot::Id::new(format!("N{}_{}", id.0, idx)).unwrap()
            }
        }
    }

    fn node_label<'b>(&'b self, n: &Nd) -> dot::LabelText<'b> {
        match n {
            AlternatingDrawNode::Node(id) => dot::LabelText::LabelStr(Cow::Borrowed(
                self.states[id.0].name.as_deref().unwrap_or_default(),
            )),
            AlternatingDrawNode::AndNode(_, _) => dot::LabelText::LabelStr(".".into()),
        }
    }

    fn node_shape<'b>(&'b self, n: &Nd) -> Option<dot::LabelText<'b>> {
        match n {
            AlternatingDrawNode::Node(_) => None,
            AlternatingDrawNode::AndNode(_, _) => Some(dot::LabelText::LabelStr("point".into())),
        }
    }

    fn node_style<'b>(&'b self, n: &Nd) -> dot::Style {
        match n {
            AlternatingDrawNode::Node(s) => match &self.acceptance {
                Acceptance::Safety => dot::Style::None,
                Acceptance::Büchi(accepting) => {
                    if accepting.contains(s) {
                        dot::Style::Filled
                    } else {
                        dot::Style::None
                    }
                }
            },
            AlternatingDrawNode::AndNode(_, _) => dot::Style::None,
        }
    }

    fn edge_label<'b>(&'b self, e: &Ed) -> dot::LabelText<'b> {
        match *e {
            AlternatingDrawEdge::NonDet(source, idx, _)
            | AlternatingDrawEdge::ToAndNode(source, idx) => {
                let expr = &self.transitions[source.0][idx].0;
                dot::LabelText::LabelStr(format!("{expr}").into())
            }
            AlternatingDrawEdge::FromAndNode(_, _, _) => dot::LabelText::LabelStr("".into()),
        }
    }

    fn edge_end_arrow(&'a self, e: &Ed) -> dot::Arrow {
        match e {
            AlternatingDrawEdge::NonDet(_, _, _) | AlternatingDrawEdge::FromAndNode(_, _, _) => {
                dot::Arrow::normal()
            }
            AlternatingDrawEdge::ToAndNode(_, _) => dot::Arrow::none(),
        }
    }
}

impl<'a, D: Domain> dot::GraphWalk<'a, Nd, Ed> for AlternatingAutomaton<D> {
    fn nodes(&self) -> dot::Nodes<'a, Nd> {
        self.states
            .iter()
            .map(|s| AlternatingDrawNode::Node(s.id))
            .chain(self.states.iter().flat_map(|s| {
                self.transitions[s.id.0]
                    .iter()
                    .enumerate()
                    .filter_map(|(idx, (_, targets))| {
                        if targets.len() > 1 {
                            Some(AlternatingDrawNode::AndNode(s.id, idx))
                        } else {
                            None
                        }
                    })
            }))
            .collect()
    }
    fn edges(&'a self) -> dot::Edges<'a, Ed> {
        Cow::Owned(
            // non-deterministic
            self.states
                .iter()
                .zip(&self.transitions)
                .flat_map(|(s, t)| {
                    t.iter()
                        .enumerate()
                        .filter(|(i, (_, states))| states.len() <= 1)
                        .flat_map(move |(i, (_, states))| {
                            states
                                .iter()
                                .map(move |&target| AlternatingDrawEdge::NonDet(s.id, i, target))
                        })
                })
                .chain(
                    // to AND node
                    self.states
                        .iter()
                        .zip(&self.transitions)
                        .flat_map(|(s, t)| {
                            t.iter()
                                .enumerate()
                                .filter(|(i, (_, states))| states.len() > 1)
                                .map(move |(i, (_, states))| {
                                    AlternatingDrawEdge::ToAndNode(s.id, i)
                                })
                        }),
                )
                .chain(
                    // from AND node
                    self.states
                        .iter()
                        .zip(&self.transitions)
                        .flat_map(|(s, t)| {
                            t.iter()
                                .enumerate()
                                .filter(|(i, (_, states))| states.len() > 1)
                                .flat_map(move |(i, (_, states))| {
                                    states.iter().map(move |&target| {
                                        AlternatingDrawEdge::FromAndNode(s.id, i, target)
                                    })
                                })
                        }),
                )
                .collect(),
        )
    }

    fn source(&self, e: &Ed) -> Nd {
        match *e {
            AlternatingDrawEdge::NonDet(source, _, _)
            | AlternatingDrawEdge::ToAndNode(source, _) => AlternatingDrawNode::Node(source),
            AlternatingDrawEdge::FromAndNode(source, idx, _) => {
                AlternatingDrawNode::AndNode(source, idx)
            }
        }
    }
    fn target(&self, e: &Ed) -> Nd {
        match *e {
            AlternatingDrawEdge::NonDet(_, _, target)
            | AlternatingDrawEdge::FromAndNode(_, _, target) => AlternatingDrawNode::Node(target),
            AlternatingDrawEdge::ToAndNode(source, idx) => {
                AlternatingDrawNode::AndNode(source, idx)
            }
        }
    }
}

//! Graphviz encoding of automata

use super::{Alternating, Automaton, Büchi, Safety};
use crate::automaton::{format_bdd, StateId};
use biodivine_lib_bdd::Bdd;
use itertools::Itertools;
use std::{borrow::Cow, collections::HashSet};

trait StateStyle {
    fn style_of(&self, _state: StateId) -> dot::Style {
        dot::Style::None
    }
}

impl<Edg> StateStyle for Automaton<Edg, Büchi> {
    fn style_of(&self, state: StateId) -> dot::Style {
        if self.acceptance.0.contains(&state) {
            dot::Style::Filled
        } else {
            dot::Style::None
        }
    }
}

impl<Edg> StateStyle for Automaton<Edg, Safety> {}

#[derive(Debug, Clone)]
pub(crate) enum DrawNode {
    Initial,
    State(StateId),
    /// A virtual node to represent AND transitions
    AndNode(StateId, HashSet<StateId>),
}

#[derive(Debug, Clone)]
pub(crate) enum DrawEdge {
    ToInitial,
    Edge(StateId, Bdd, StateId),
    ToAndNode(StateId, Bdd, HashSet<StateId>),
    FromAndNode(StateId, HashSet<StateId>, StateId),
}

type Nd = DrawNode;
type Ed = DrawEdge;

impl<'a, Edg, Acc> dot::Labeller<'a, Nd, Ed> for Automaton<Edg, Acc>
where
    Self: StateStyle,
    // &'a Edg: IntoIterator<Item = (&'a StateId, &'a Bdd)> + 'a,
    // Edg: for<'x> std::ops::Index<&'x StateId, Output = Bdd> + 'a,
{
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("automaton").unwrap()
    }

    fn node_id(&'a self, n: &Nd) -> dot::Id<'a> {
        match n {
            DrawNode::Initial => dot::Id::new("_init".to_string()).unwrap(),
            DrawNode::State(s) => dot::Id::new(format!("N{}", s.0)).unwrap(),
            DrawNode::AndNode(s, t) => {
                let canonical: Vec<_> = t
                    .iter()
                    .copied()
                    .sorted()
                    .map(|s| s.0.to_string())
                    .collect();
                dot::Id::new(format!("A{}__{}", s.0, canonical.join("_"))).unwrap()
            }
        }
    }

    fn node_label<'b>(&'b self, n: &Nd) -> dot::LabelText<'b> {
        match n {
            DrawNode::Initial => dot::LabelText::LabelStr("".into()),
            DrawNode::State(s) => dot::LabelText::LabelStr(Cow::Borrowed(
                self.states[s.0].name.as_deref().unwrap_or_default(),
            )),
            DrawNode::AndNode(_, _) => dot::LabelText::LabelStr(".".into()),
        }
    }

    fn node_shape<'b>(&'b self, n: &Nd) -> Option<dot::LabelText<'b>> {
        match n {
            DrawNode::Initial | DrawNode::State(_) => None,
            DrawNode::AndNode(_, _) => Some(dot::LabelText::LabelStr("point".into())),
        }
    }

    fn node_style(&self, n: &Nd) -> dot::Style {
        match n {
            DrawNode::Initial => dot::Style::Invisible,
            DrawNode::State(s) => self.style_of(*s),
            DrawNode::AndNode(_, _) => dot::Style::None,
        }
    }

    fn edge_label<'b>(&'b self, e: &Ed) -> dot::LabelText<'b> {
        match e {
            DrawEdge::ToInitial | DrawEdge::FromAndNode(_, _, _) => {
                dot::LabelText::LabelStr(String::new().into())
            }
            DrawEdge::Edge(_, guard, _) | DrawEdge::ToAndNode(_, guard, _) => {
                let dnf = format_bdd(guard, &self.variables);

                dot::LabelText::LabelStr(dnf.into())
            }
        }
    }
}

impl<'a, Edg, Acc> dot::GraphWalk<'a, Nd, Ed> for Automaton<Edg, Acc>
where
    Self: StateStyle,
    &'a Edg: IntoIterator<Item = (&'a StateId, &'a Bdd)> + 'a,
    Edg: for<'x> std::ops::Index<&'x StateId, Output = Bdd> + 'a,
{
    fn nodes(&self) -> dot::Nodes<'a, Nd> {
        self.states
            .iter()
            .map(|s| DrawNode::State(s.id))
            .chain(std::iter::once(DrawNode::Initial))
            .collect()
    }

    fn edges(&'a self) -> dot::Edges<'a, Ed> {
        Cow::Owned(
            // non-deterministic
            self.states
                .iter()
                .zip(&self.transitions)
                .flat_map(|(s, t)| {
                    t.into_iter()
                        .map(move |(target, guard)| DrawEdge::Edge(s.id, guard.clone(), *target))
                })
                .chain(std::iter::once(DrawEdge::ToInitial))
                .collect(),
        )
    }

    fn source(&self, e: &Ed) -> Nd {
        e.source()
    }

    fn target(&self, e: &Ed) -> Nd {
        e.target(self.initial_state)
    }
}

impl<'a, Acc> dot::GraphWalk<'a, Nd, Ed> for Automaton<Alternating, Acc>
where
    Self: StateStyle,
{
    fn nodes(&self) -> dot::Nodes<'a, Nd> {
        self.states
            .iter()
            .map(|s| DrawNode::State(s.id))
            .chain(self.states.iter().flat_map(|s| {
                self.transitions[s.id.0]
                    .0
                    .iter()
                    .filter_map(|(_, targets)| {
                        if targets.len() > 1 {
                            Some(DrawNode::AndNode(s.id, targets.clone()))
                        } else {
                            None
                        }
                    })
            }))
            .chain(std::iter::once(DrawNode::Initial))
            .collect()
    }

    fn edges(&'a self) -> dot::Edges<'a, Ed> {
        Cow::Owned(
            // non-deterministic
            self.states
                .iter()
                .zip(&self.transitions)
                .flat_map(|(s, t)| {
                    t.0.iter().filter(|(_, states)| states.len() <= 1).flat_map(
                        move |(guard, states)| {
                            states
                                .iter()
                                .map(move |&target| DrawEdge::Edge(s.id, guard.clone(), target))
                        },
                    )
                })
                .chain(
                    // to AND node
                    self.states
                        .iter()
                        .zip(&self.transitions)
                        .flat_map(|(s, t)| {
                            t.0.iter().filter(|(_, states)| states.len() > 1).map(
                                move |(guard, states)| {
                                    DrawEdge::ToAndNode(s.id, guard.clone(), states.clone())
                                },
                            )
                        }),
                )
                .chain(
                    // from AND node
                    self.states
                        .iter()
                        .zip(&self.transitions)
                        .flat_map(|(s, t)| {
                            t.0.iter().filter(|(_, states)| states.len() > 1).flat_map(
                                move |(_, states)| {
                                    states.iter().map(move |&target| {
                                        DrawEdge::FromAndNode(s.id, states.clone(), target)
                                    })
                                },
                            )
                        }),
                )
                .chain(std::iter::once(DrawEdge::ToInitial))
                .collect(),
        )
    }

    fn source(&self, e: &Ed) -> Nd {
        e.source()
    }

    fn target(&self, e: &Ed) -> Nd {
        e.target(self.initial_state)
    }
}

impl DrawEdge {
    fn source(&self) -> DrawNode {
        match self {
            Self::ToInitial => DrawNode::Initial,
            Self::Edge(source, _, _) | Self::ToAndNode(source, _, _) => DrawNode::State(*source),
            Self::FromAndNode(source, and, _) => DrawNode::AndNode(*source, and.clone()),
        }
    }

    fn target(&self, initial: StateId) -> DrawNode {
        match self {
            Self::ToInitial => DrawNode::State(initial),
            Self::Edge(_, _, target) | Self::FromAndNode(_, _, target) => DrawNode::State(*target),
            Self::ToAndNode(source, _, target) => DrawNode::AndNode(*source, target.clone()),
        }
    }
}

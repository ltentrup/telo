use crate::automaton::{format_bdd, AlternatingBüchiAutomaton, StateId};
use std::borrow::Cow;

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

impl<'a> dot::Labeller<'a, Nd, Ed> for AlternatingBüchiAutomaton {
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
            AlternatingDrawNode::Node(s) => {
                if self.acceptance.0.contains(s) {
                    dot::Style::Filled
                } else {
                    dot::Style::None
                }
            }
            AlternatingDrawNode::AndNode(_, _) => dot::Style::None,
        }
    }

    fn edge_label<'b>(&'b self, e: &Ed) -> dot::LabelText<'b> {
        match *e {
            AlternatingDrawEdge::NonDet(source, idx, _)
            | AlternatingDrawEdge::ToAndNode(source, idx) => {
                let expr = &self.transitions[source.0][idx].0;
                let dnf = format_bdd(expr, &self.variables);

                dot::LabelText::LabelStr(format!("{dnf}").into())
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

impl<'a> dot::GraphWalk<'a, Nd, Ed> for AlternatingBüchiAutomaton {
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

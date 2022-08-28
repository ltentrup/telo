use biodivine_lib_bdd::Bdd;

use crate::automaton::{
    format_bdd, NonDeterministicBüchiAutomaton, NonDeterministicSafetyAutomaton, StateId,
};
use std::borrow::Cow;

use super::{Automaton, NonDeterministic, Safety};

trait StateStyle {
    fn style_of(&self, _state: &StateId) -> dot::Style {
        dot::Style::None
    }
}

impl StateStyle for NonDeterministicBüchiAutomaton {
    fn style_of(&self, state: &StateId) -> dot::Style {
        if self.acceptance.0.contains(state) {
            dot::Style::Filled
        } else {
            dot::Style::None
        }
    }
}
impl<Edg> StateStyle for Automaton<Edg, Safety> {}

#[derive(Debug, Clone, Copy)]
pub(crate) enum DrawNode {
    Initial,
    State(StateId),
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum DrawEdge {
    ToInitial,
    Edge(StateId, StateId),
}

type Nd = DrawNode;
type Ed = DrawEdge;

impl<'a, Edg, Acc> dot::Labeller<'a, Nd, Ed> for Automaton<Edg, Acc>
where
    Self: StateStyle,
    &'a Edg: IntoIterator<Item = (&'a StateId, &'a Bdd)> + 'a,
    Edg: for<'x> std::ops::Index<&'x StateId, Output = Bdd> + 'a,
{
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("nondeterministic").unwrap()
    }

    fn node_id(&'a self, n: &Nd) -> dot::Id<'a> {
        match n {
            DrawNode::Initial => dot::Id::new(format!("_init")).unwrap(),
            DrawNode::State(s) => dot::Id::new(format!("N{}", s.0)).unwrap(),
        }
    }

    fn node_label<'b>(&'b self, n: &Nd) -> dot::LabelText<'b> {
        match n {
            DrawNode::Initial => dot::LabelText::LabelStr("".into()),
            DrawNode::State(s) => dot::LabelText::LabelStr(Cow::Borrowed(
                self.states[s.0].name.as_deref().unwrap_or_default(),
            )),
        }
    }

    fn node_style<'b>(&'b self, n: &Nd) -> dot::Style {
        match n {
            DrawNode::Initial => dot::Style::Invisible,
            DrawNode::State(s) => self.style_of(s),
        }
    }

    fn edge_label<'b>(&'b self, e: &Ed) -> dot::LabelText<'b> {
        match e {
            DrawEdge::ToInitial => dot::LabelText::LabelStr(format!("").into()),
            DrawEdge::Edge(source, target) => {
                let expr = &self.transitions[source.0][target];
                let dnf = format_bdd(expr, &self.variables);

                dot::LabelText::LabelStr(format!("{dnf}").into())
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
                        .map(move |(target, _)| DrawEdge::Edge(s.id, *target))
                })
                .chain(std::iter::once(DrawEdge::ToInitial))
                .collect(),
        )
    }

    fn source(&self, e: &Ed) -> Nd {
        match e {
            DrawEdge::ToInitial => DrawNode::Initial,
            DrawEdge::Edge(source, _) => DrawNode::State(*source),
        }
    }

    fn target(&self, e: &Ed) -> Nd {
        match e {
            DrawEdge::ToInitial => DrawNode::State(self.initial_state),
            DrawEdge::Edge(_, target) => DrawNode::State(*target),
        }
    }
}

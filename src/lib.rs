//! # Temporal Specifications in Rust
//!
//! Translation steps:
//! * Safety LTL over arbitrary domain
//! * Negation No&rmal Form
//! * Alternating-time safety automaton
//! * Deterministic safety automaton

pub(crate) mod automaton;

use automaton::{AlternatingAutomaton, AlternatingEdge, StateId};
use std::{fmt::Display, rc::Rc};

pub trait Domain: PartialEq + 'static {}

pub trait Proposition<D: Domain>: 'static {
    fn eval(&self, value: D) -> bool;
}

#[derive(Debug)]
struct AtomicProposition<D: Domain> {
    value: D,
}

impl<D: Domain> Proposition<D> for AtomicProposition<D> {
    fn eval(&self, value: D) -> bool {
        self.value == value
    }
}

impl<D: Domain, F: Fn(D) -> bool + 'static> Proposition<D> for F {
    fn eval(&self, value: D) -> bool {
        self(value)
    }
}

/// A proposition over an arbitrary expression.
pub struct ExpressionProposition<D: Domain> {
    name: &'static str,
    closure: Box<dyn Fn(D) -> bool + 'static>,
}

impl<D: Domain> Proposition<D> for ExpressionProposition<D> {
    fn eval(&self, value: D) -> bool {
        (self.closure)(value)
    }
}

impl<D: Domain> std::fmt::Display for ExpressionProposition<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl<D: Domain> ExpressionProposition<D> {
    fn make_true() -> Self {
        Self {
            name: "true",
            closure: Box::new(|_| true),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct PropertyId(usize);

#[derive(Clone)]
pub enum Property<D: Domain> {
    // boolean
    Atomic(Rc<ExpressionProposition<D>>),
    Not(Rc<Self>),
    And(Rc<Self>, Rc<Self>),
    Or(Rc<Self>, Rc<Self>),

    // temporal
    Always(Rc<Self>),
    Finally(Rc<Self>),
    Next(Rc<Self>),
}

impl<D: Domain> Property<D> {
    fn atomic(expr: ExpressionProposition<D>) -> Self {
        Self::Atomic(Rc::new(expr))
    }

    fn not<I: Into<Self>>(inner: I) -> Self {
        Self::Not(Rc::new(inner.into()))
    }

    fn implies<C>(self, conclusion: C) -> Self
    where
        C: Into<Self>,
    {
        Self::Or(
            Rc::new(Self::Not(Rc::new(self))),
            Rc::new(conclusion.into()),
        )
    }

    fn or<C>(self, other: C) -> Self
    where
        C: Into<Self>,
    {
        Self::Or(Rc::new(self), Rc::new(other.into()))
    }

    fn and<C>(self, other: C) -> Self
    where
        C: Into<Self>,
    {
        Self::And(Rc::new(self), Rc::new(other.into()))
    }

    fn always<I: Into<Self>>(inner: I) -> Self {
        Self::Always(Rc::new(inner.into()))
    }

    fn next(inner: Self) -> Self {
        Self::Next(Rc::new(inner))
    }
}

impl<D: Domain> Property<D> {
    fn is_in_nnf(&self) -> bool {
        match self {
            Property::Atomic(_) => true,
            Property::Not(subf) => match subf.as_ref() {
                Property::Atomic(_) => true,
                _ => false,
            },
            Property::And(lhs, rhs) | Property::Or(lhs, rhs) => lhs.is_in_nnf() && rhs.is_in_nnf(),
            Property::Always(subf) | Property::Finally(subf) | Property::Next(subf) => {
                subf.is_in_nnf()
            }
        }
    }

    fn to_nnf(&self) -> Self {
        self.to_nnf_core(false)
    }

    fn to_nnf_core(&self, negated: bool) -> Self {
        match self {
            Property::Atomic(a) => {
                if negated {
                    Self::Not(Rc::new(Property::Atomic(a.clone())))
                } else {
                    Property::Atomic(a.clone())
                }
            }
            Property::Not(subf) => subf.to_nnf_core(!negated),
            Property::And(lhs, rhs) => {
                let lhs = Rc::new(lhs.to_nnf_core(negated));
                let rhs = Rc::new(rhs.to_nnf_core(negated));
                if negated {
                    Property::Or(lhs, rhs)
                } else {
                    Property::And(lhs, rhs)
                }
            }
            Property::Or(lhs, rhs) => {
                let lhs = Rc::new(lhs.to_nnf_core(negated));
                let rhs = Rc::new(rhs.to_nnf_core(negated));
                if negated {
                    Property::And(lhs, rhs)
                } else {
                    Property::Or(lhs, rhs)
                }
            }
            Property::Always(subf) => {
                let subf = Rc::new(subf.to_nnf_core(negated));
                if negated {
                    Property::Finally(subf)
                } else {
                    Property::Always(subf)
                }
            }
            Property::Finally(subf) => {
                let subf = Rc::new(subf.to_nnf_core(negated));
                if negated {
                    Property::Always(subf)
                } else {
                    Property::Finally(subf)
                }
            }
            Property::Next(subf) => {
                let subf = Rc::new(subf.to_nnf_core(negated));
                Property::Next(subf)
            }
        }
    }
}

impl<D: Domain> std::fmt::Display for Property<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Property::Atomic(expr) => write!(f, "({})", expr),
            Property::Not(subf) => write!(f, "¬{}", subf),
            Property::And(lhs, rhs) => write!(f, "({} ∧ {})", lhs, rhs),
            Property::Or(lhs, rhs) => write!(f, "({} ∨ {})", lhs, rhs),
            Property::Always(subf) => write!(f, "G {}", subf),
            Property::Finally(subf) => write!(f, "F {}", subf),
            Property::Next(subf) => write!(f, "X {}", subf),
        }
    }
}

impl<D: Domain> Property<D> {
    fn to_alternating_büchi(&self) -> AlternatingAutomaton<D> {
        assert!(self.is_in_nnf());
        let mut automaton = AlternatingAutomaton::new_büchi();
        let initial_state = self.to_alternating_büchi_state(&mut automaton);
        automaton.set_initial(initial_state);

        automaton
    }

    fn to_alternating_büchi_state(&self, automaton: &mut AlternatingAutomaton<D>) -> StateId {
        let state = automaton.new_state(Some(&format!("{}", self)));
        match self {
            Property::Atomic(expr) => {
                automaton.add_edge(state, (expr.clone(), vec![automaton.accepting_sink()]))
            }
            Property::Not(_) => todo!(),
            Property::And(_, _) => todo!(),
            Property::Or(lhs, rhs) => {
                let lhs = lhs.to_alternating_büchi_edge(automaton);
                let rhs = rhs.to_alternating_büchi_edge(automaton);
                for edge in lhs.iter().chain(&rhs) {
                    automaton.add_edge(state, edge.clone());
                }
            }
            Property::Always(subf) => {
                let edges = subf.to_alternating_büchi_edge(automaton);
                for mut edge in edges {
                    // since the constraint is conjunctive, we can remove edges to the accepting sink
                    edge.1.retain(|&s| s != automaton.accepting_sink());
                    edge.1.push(state);
                    automaton.add_edge(state, edge);
                }
                automaton.add_accepting(state);
            }
            Property::Finally(_) => todo!(),
            Property::Next(subf) => {
                let next_state = subf.to_alternating_büchi_state(automaton);
                automaton.add_edge(
                    state,
                    (ExpressionProposition::make_true().into(), vec![next_state]),
                );
            }
        }

        state
    }

    fn to_alternating_büchi_edge(
        &self,
        automaton: &mut AlternatingAutomaton<D>,
    ) -> AlternatingEdge<D> {
        match self {
            Property::Atomic(expr) => {
                return vec![(expr.clone(), vec![automaton.accepting_sink()])];
            }
            Property::Not(_) => todo!(),
            Property::And(_, _) => todo!(),
            Property::Or(lhs, rhs) => {
                let mut lhs = lhs.to_alternating_büchi_edge(automaton);
                let mut rhs = rhs.to_alternating_büchi_edge(automaton);
                lhs.append(&mut rhs);
                return lhs;
            }
            Property::Always(_) => todo!(),
            Property::Finally(_) => todo!(),
            Property::Next(subf) => {
                let state = subf.to_alternating_büchi_state(automaton);
                return vec![(ExpressionProposition::make_true().into(), vec![state])];
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::automaton::Automaton;

    use super::*;

    #[test]
    fn simple() {
        #[derive(Debug, PartialEq, Eq)]
        enum Observation {
            A,
            B,
        }

        impl Domain for Observation {}

        // let eq_b = ExpressionProposition {
        //     name: "obs == B",
        //     closure: Box::new(|p| p == Observation::B),
        // };
        let neq_b = ExpressionProposition {
            name: "obs != B",
            closure: Box::new(|p| p != Observation::B),
        };
        // let eq_a = ExpressionProposition {
        //     name: "obs == A",
        //     closure: Box::new(|p| p == Observation::A),
        // };
        let neq_a = ExpressionProposition {
            name: "obs != A",
            closure: Box::new(|p| p != Observation::A),
        };

        // let prop: Property<Observation> = Property::always(Property::atomic(eq_b).implies(
        //     Property::next(Property::always(Property::not(Property::atomic(eq_a)))),
        // ));
        // let prop: Property<Observation> =
        //     Property::next(Property::or(Property::atomic(eq_a), Property::atomic(eq_b)));
        // let prop: Property<Observation> = Property::always(Property::atomic(eq_b));
        let prop: Property<Observation> = Property::always(
            Property::atomic(neq_b).or(Property::next(Property::always(Property::atomic(neq_a)))),
        );

        println!("{}", prop);
        println!("{}", prop.to_nnf());

        let büchi = prop.to_nnf().to_alternating_büchi();
        let mut s = Vec::new();
        dot::render(&büchi, &mut s).unwrap();
        let s = String::from_utf8(s).unwrap();
        println!("{s}");
        let büchi = Automaton::from(&büchi);

        panic!();

        // target syntax:
        // let prop: Property<Observation> = property!(p, always ((p == Observation::B) -> next always (p != Observation::A)));
    }
}

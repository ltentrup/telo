//! # Temporal Specifications in Rust
//!
//! Translation steps:
//! * Safety LTL over arbitrary domain
//! * Negation No&rmal Form
//! * Alternating-time safety automaton
//! * Deterministic safety automaton

#![deny(clippy::all)]
#![warn(clippy::pedantic, clippy::nursery, clippy::cargo)]

pub(crate) mod automaton;
pub(crate) mod monitor;

use automaton::{AlternatingBüchiAutomaton, StateId};
use biodivine_lib_bdd::{Bdd, BddValuation, BddVariable, BddVariableSet, BddVariableSetBuilder};
use itertools::Itertools;
use maplit::hashset;
use std::{cell::RefCell, collections::HashSet, ops::Deref, rc::Rc};

pub trait Domain: 'static {}

/// A predicate maps values from [`Domain`] to a boolean value.
pub trait Predicate<D: Domain>: 'static {
    fn eval(&self, value: &D) -> bool;
}

/// A predicate representing an equality constraint over the provided value.
#[derive(Debug)]
struct EqPredicate<D: Domain + PartialEq> {
    value: D,
}

impl<D: Domain + PartialEq> Predicate<D> for EqPredicate<D> {
    fn eval(&self, value: &D) -> bool {
        self.value == *value
    }
}

impl<D: Domain, F: Fn(&D) -> bool + 'static> Predicate<D> for F {
    fn eval(&self, value: &D) -> bool {
        self(value)
    }
}

/// A predicate computed by the provided closure.
pub struct ClosurePredicate<D: Domain> {
    name: &'static str,
    closure: Box<dyn Fn(&D) -> bool + 'static>,
}

impl<D: Domain> Predicate<D> for ClosurePredicate<D> {
    fn eval(&self, value: &D) -> bool {
        (self.closure)(value)
    }
}

impl<D: Domain> std::fmt::Display for ClosurePredicate<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

struct PredicatesBuilder<D: Domain>(Vec<ClosurePredicate<D>>);

pub struct Predicates<D: Domain> {
    predicates: Vec<ClosurePredicate<D>>,
    variables: Vec<BddVariable>,
    manager: BddVariableSet,
}

pub struct PropertyBuilder<D: Domain> {
    predicates: Predicates<D>,
    properties: Vec<PropertyAst>,
}

#[derive(Clone)]
pub struct PropertyBuilder2<D: Domain>(Rc<RefCell<PropertyBuilder<D>>>);

impl<D: Domain> Default for PredicatesBuilder<D> {
    fn default() -> Self {
        Self(Vec::default())
    }
}

impl<D: Domain> Predicates<D> {
    fn builder() -> PredicatesBuilder<D> {
        PredicatesBuilder::default()
    }

    fn evaluate(&self, observation: &D) -> BddValuation {
        BddValuation::new(
            self.predicates
                .iter()
                .map(|predicate| predicate.eval(observation))
                .collect(),
        )
    }

    fn bdd_variable(&self, predicate: PredicateId) -> &BddVariable {
        &self.variables[predicate.0]
    }

    fn bdd_manager(&self) -> &BddVariableSet {
        &self.manager
    }
}

impl<D: Domain> PredicatesBuilder<D> {
    fn new_predicate(&mut self, predicate: ClosurePredicate<D>) -> PredicateId {
        let id = PredicateId(self.0.len());
        self.0.push(predicate);
        id
    }

    fn build(self) -> Predicates<D> {
        let mut builder = BddVariableSetBuilder::new();
        let variables = self
            .0
            .iter()
            .map(|proposition| builder.make_variable(&format!("{proposition}")))
            .collect();
        Predicates {
            predicates: self.0,
            variables,
            manager: builder.build(),
        }
    }
}

impl<D: Domain> std::ops::Index<PredicateId> for Predicates<D> {
    type Output = ClosurePredicate<D>;

    fn index(&self, index: PredicateId) -> &Self::Output {
        &self.predicates[index.0]
    }
}

impl<D: Domain> PropertyBuilder2<D> {
    pub fn new(predicates: Predicates<D>) -> Self {
        Self(Rc::new(RefCell::new(PropertyBuilder::new(predicates))))
    }

    pub fn atomic(&mut self, predicate: PredicateId) -> Property<D> {
        Property {
            builder: self.0.clone(),
            property: self.0.borrow_mut().atomic(predicate),
        }
    }
}

impl<D: Domain> PropertyBuilder<D> {
    fn new(predicates: Predicates<D>) -> Self {
        Self {
            predicates,
            properties: Vec::default(),
        }
    }

    fn add(&mut self, ast: PropertyAst) -> PropertyId {
        let id = PropertyId(self.properties.len());
        self.properties.push(ast);
        id
    }

    fn atomic(&mut self, predicate: PredicateId) -> PropertyId {
        self.add(PropertyAst::Atomic(predicate))
    }

    fn not(&mut self, property: PropertyId) -> PropertyId {
        self.add(PropertyAst::Not(property))
    }

    fn and(&mut self, left: PropertyId, right: PropertyId) -> PropertyId {
        self.add(PropertyAst::And(left, right))
    }

    fn or(&mut self, left: PropertyId, right: PropertyId) -> PropertyId {
        self.add(PropertyAst::Or(left, right))
    }

    fn implies(&mut self, premise: PropertyId, conclusion: PropertyId) -> PropertyId {
        let premise = self.add(PropertyAst::Not(premise));
        self.add(PropertyAst::Or(premise, conclusion))
    }

    fn always(&mut self, property: PropertyId) -> PropertyId {
        self.add(PropertyAst::Always(property))
    }

    fn finally(&mut self, property: PropertyId) -> PropertyId {
        self.add(PropertyAst::Finally(property))
    }

    fn next(&mut self, property: PropertyId) -> PropertyId {
        self.add(PropertyAst::Next(property))
    }

    // fn bdd_variables(&self) -> (Vec<BddVariable>, BddVariableSet) {
    //     let mut builder = BddVariableSetBuilder::new();
    //     let variables = self
    //         .predicates
    //         .0
    //         .iter()
    //         .map(|proposition| builder.make_variable(&format!("{proposition}")))
    //         .collect();
    //     (variables, builder.build())
    // }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PredicateId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PropertyId(usize);

#[derive(Debug, Clone, Copy)]
enum PropertyAst {
    // boolean
    Atomic(PredicateId),
    Not(PropertyId),
    And(PropertyId, PropertyId),
    Or(PropertyId, PropertyId),

    // temporal
    Always(PropertyId),
    Finally(PropertyId),
    Next(PropertyId),
}

#[derive(Clone)]
pub struct Property<D: Domain> {
    builder: Rc<RefCell<PropertyBuilder<D>>>,
    property: PropertyId,
}

impl<D: Domain> std::ops::BitAnd for Property<D> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self {
            builder: self.builder.clone(),
            property: self.builder.borrow_mut().and(self.property, rhs.property),
        }
    }
}

impl<D: Domain> std::ops::Not for Property<D> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self {
            builder: self.builder.clone(),
            property: self.builder.borrow_mut().not(self.property),
        }
    }
}

impl<D: Domain> Property<D> {
    pub fn implies(&self, conclusion: &Self) -> Self {
        assert!(std::rc::Rc::ptr_eq(&self.builder, &conclusion.builder));
        Self {
            builder: self.builder.clone(),
            property: self
                .builder
                .borrow_mut()
                .implies(self.property, conclusion.property),
        }
    }

    pub fn next(property: &Self) -> Self {
        Self {
            builder: property.builder.clone(),
            property: property.builder.borrow_mut().next(property.property),
        }
    }

    pub fn always(property: &Self) -> Self {
        Self {
            builder: property.builder.clone(),
            property: property.builder.borrow_mut().always(property.property),
        }
    }

    pub fn finally(property: &Self) -> Self {
        Self {
            builder: property.builder.clone(),
            property: property.builder.borrow_mut().finally(property.property),
        }
    }

    /// Returns true when the formula is in negation normal form.
    pub fn is_nnf(&self) -> bool {
        self.builder.deref().borrow().is_in_nnf(self.property)
    }

    /// Returns a new formula that accepts the same language and is in
    /// negation normal form. The size of the new formula is at most
    /// 2 times larger than the original formula.
    pub fn to_nnf(&self) -> Self {
        let property = self.builder.deref().borrow_mut().to_nnf(self.property);
        Self {
            builder: self.builder.clone(),
            property,
        }
    }

    pub(crate) fn to_alternating_büchi(&self) -> AlternatingBüchiAutomaton {
        self.builder
            .deref()
            .borrow()
            .to_alternating_büchi(self.property)
    }
}

impl<D: Domain> std::fmt::Display for Property<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let builder = self.builder.deref().borrow();
        write!(f, "{}", builder.to_string(self.property))
    }
}

impl<D: Domain> PropertyBuilder<D> {
    fn is_in_nnf(&self, property: PropertyId) -> bool {
        match self.properties[property.0] {
            PropertyAst::Atomic(_) => true,
            PropertyAst::Not(subf) => matches!(self.properties[subf.0], PropertyAst::Atomic(_)),
            PropertyAst::And(lhs, rhs) | PropertyAst::Or(lhs, rhs) => {
                self.is_in_nnf(lhs) && self.is_in_nnf(rhs)
            }
            PropertyAst::Always(subf) | PropertyAst::Finally(subf) | PropertyAst::Next(subf) => {
                self.is_in_nnf(subf)
            }
        }
    }

    fn to_nnf(&mut self, property: PropertyId) -> PropertyId {
        self.to_nnf_core(property, false)
    }

    fn to_nnf_core(&mut self, property: PropertyId, negated: bool) -> PropertyId {
        match self.properties[property.0] {
            PropertyAst::Atomic(a) => {
                if negated {
                    self.add(PropertyAst::Not(property))
                } else {
                    property
                }
            }
            PropertyAst::Not(subf) => self.to_nnf_core(subf, !negated),
            PropertyAst::And(lhs, rhs) => {
                let lhs = self.to_nnf_core(lhs, negated);
                let rhs = self.to_nnf_core(rhs, negated);
                self.add(if negated {
                    PropertyAst::Or(lhs, rhs)
                } else {
                    PropertyAst::And(lhs, rhs)
                })
            }
            PropertyAst::Or(lhs, rhs) => {
                let lhs = self.to_nnf_core(lhs, negated);
                let rhs = self.to_nnf_core(rhs, negated);
                self.add(if negated {
                    PropertyAst::And(lhs, rhs)
                } else {
                    PropertyAst::Or(lhs, rhs)
                })
            }
            PropertyAst::Always(subf) => {
                let subf = self.to_nnf_core(subf, negated);
                self.add(if negated {
                    PropertyAst::Finally(subf)
                } else {
                    PropertyAst::Always(subf)
                })
            }
            PropertyAst::Finally(subf) => {
                let subf = self.to_nnf_core(subf, negated);
                self.add(if negated {
                    PropertyAst::Always(subf)
                } else {
                    PropertyAst::Finally(subf)
                })
            }
            PropertyAst::Next(subf) => {
                let subf = self.to_nnf_core(subf, negated);
                self.add(PropertyAst::Next(subf))
            }
        }
    }
}

impl<D: Domain> PropertyBuilder<D> {
    fn to_string(&self, property: PropertyId) -> String {
        match self.properties[property.0] {
            PropertyAst::Atomic(expr) => format!("({})", self.predicates[expr]),
            PropertyAst::Not(subf) => format!("!{}", self.to_string(subf)),
            PropertyAst::And(lhs, rhs) => {
                format!("({} & {})", self.to_string(lhs), self.to_string(rhs))
            }
            PropertyAst::Or(lhs, rhs) => {
                format!("({} | {})", self.to_string(lhs), self.to_string(rhs))
            }
            PropertyAst::Always(subf) => format!("G {}", self.to_string(subf)),
            PropertyAst::Finally(subf) => format!("F {}", self.to_string(subf)),
            PropertyAst::Next(subf) => format!("X {}", self.to_string(subf)),
        }
    }
}

impl<D: Domain> PropertyBuilder<D> {
    fn to_alternating_büchi(&self, property: PropertyId) -> AlternatingBüchiAutomaton {
        assert!(self.is_in_nnf(property));
        let variables = &self.predicates.variables;
        let set = &self.predicates.manager;
        let mut automaton = AlternatingBüchiAutomaton::new_büchi(set);
        let initial_state =
            self.to_alternating_büchi_state(variables, set, &mut automaton, property);
        automaton.set_initial(initial_state);
        automaton
    }

    fn to_alternating_büchi_state(
        &self,
        variables: &[BddVariable],
        set: &BddVariableSet,
        automaton: &mut AlternatingBüchiAutomaton,
        property: PropertyId,
    ) -> StateId {
        let state = automaton.new_state(Some(&self.to_string(property)));
        match self.properties[property.0] {
            PropertyAst::Atomic(prop) => automaton.add_edge(
                state,
                set.mk_literal(variables[prop.0], true),
                hashset! {automaton.accepting_sink()},
            ),
            PropertyAst::Not(subf) => match self.properties[subf.0] {
                PropertyAst::Atomic(prop) => automaton.add_edge(
                    state,
                    set.mk_literal(variables[prop.0], false),
                    hashset! {automaton.accepting_sink()},
                ),
                _ => unreachable!("formula is in negation normal form"),
            },
            PropertyAst::And(lhs, rhs) => {
                let lhs = self.to_alternating_büchi_edge(variables, set, automaton, lhs);
                let rhs = self.to_alternating_büchi_edge(variables, set, automaton, rhs);
                for ((left_guard, left_target), (right_guard, right_target)) in
                    lhs.iter().cartesian_product(&rhs)
                {
                    let guard = left_guard.and(right_guard);
                    let target = left_target.iter().chain(right_target).copied().collect();
                    automaton.add_edge(state, guard, target);
                }
            }
            PropertyAst::Or(lhs, rhs) => {
                let lhs = self.to_alternating_büchi_edge(variables, set, automaton, lhs);
                let rhs = self.to_alternating_büchi_edge(variables, set, automaton, rhs);
                for (guard, target) in lhs.iter().chain(&rhs) {
                    automaton.add_edge(state, guard.clone(), target.clone());
                }
            }
            PropertyAst::Always(subf) => {
                let edges = self.to_alternating_büchi_edge(variables, set, automaton, subf);
                for (guard, mut target) in edges {
                    // since the constraint is conjunctive, we can remove edges to the accepting sink
                    target.retain(|&s| s != automaton.accepting_sink());
                    target.insert(state);
                    automaton.add_edge(state, guard, target);
                }
                automaton.add_accepting(state);
            }
            PropertyAst::Finally(subf) => {
                let edges = self.to_alternating_büchi_edge(variables, set, automaton, subf);
                for (guard, target) in edges {
                    automaton.add_edge(state, guard, target);
                }
                automaton.add_edge(state, set.mk_true(), hashset! {state});
            }
            PropertyAst::Next(subf) => {
                let next_state = self.to_alternating_büchi_state(variables, set, automaton, subf);
                automaton.add_edge(state, set.mk_true(), hashset! {next_state});
            }
        }

        state
    }

    fn to_alternating_büchi_edge(
        &self,
        variables: &[BddVariable],
        set: &BddVariableSet,
        automaton: &mut AlternatingBüchiAutomaton,
        property: PropertyId,
    ) -> Vec<(Bdd, HashSet<StateId>)> {
        match self.properties[property.0] {
            PropertyAst::Atomic(prop) => {
                vec![(
                    set.mk_literal(variables[prop.0], true),
                    hashset! {automaton.accepting_sink()},
                )]
            }
            PropertyAst::Not(subf) => match self.properties[subf.0] {
                PropertyAst::Atomic(prop) => {
                    vec![(
                        set.mk_literal(variables[prop.0], false),
                        hashset! {automaton.accepting_sink()},
                    )]
                }
                _ => unreachable!("formula is in negation normal form"),
            },
            PropertyAst::And(_, _) => todo!(),
            PropertyAst::Or(lhs, rhs) => {
                let mut lhs = self.to_alternating_büchi_edge(variables, set, automaton, lhs);
                let mut rhs = self.to_alternating_büchi_edge(variables, set, automaton, rhs);
                lhs.append(&mut rhs);
                lhs
            }
            PropertyAst::Always(_) => todo!(),
            PropertyAst::Finally(_) => todo!(),
            PropertyAst::Next(subf) => {
                let state = self.to_alternating_büchi_state(variables, set, automaton, subf);
                vec![(set.mk_true(), hashset! {state})]
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automaton::{NonDeterministicBüchiAutomaton, NonDeterministicSafetyAutomaton};

    #[derive(Debug, PartialEq, Eq)]
    pub(crate) enum TestObs {
        A,
        B,
    }

    impl Domain for TestObs {}

    pub(crate) fn predicates() -> Predicates<TestObs> {
        let mut builder = Predicates::builder();
        let eq_a = builder.new_predicate(ClosurePredicate {
            name: "obs is equal to A",
            closure: Box::new(|p: &TestObs| *p == TestObs::A),
        });
        let eq_b = builder.new_predicate(ClosurePredicate {
            name: "obs is equal to B",
            closure: Box::new(|p| *p == TestObs::B),
        });
        builder.build()
    }

    #[test]
    fn simple() {
        let predicates = predicates();
        let eq_a = PredicateId(0);
        let eq_b = PredicateId(1);

        let mut builder = PropertyBuilder2::new(predicates);

        let prop = Property::always(
            &builder
                .atomic(eq_b)
                .implies(&Property::next(&Property::always(&!builder.atomic(eq_a)))),
        );
        // let prop = Property::finally(&builder.atomic(eq_a));

        println!("{prop}");

        let nnf = prop.to_nnf();
        println!("{prop}");

        let büchi = nnf.to_alternating_büchi();
        let mut s = Vec::new();
        dot::render(&büchi, &mut s).unwrap();
        let s = String::from_utf8(s).unwrap();
        println!("{s}");
        let büchi = NonDeterministicBüchiAutomaton::from(&büchi);
        let mut s = Vec::new();
        dot::render(&büchi, &mut s).unwrap();
        let s = String::from_utf8(s).unwrap();
        println!("{s}");

        let safety = NonDeterministicSafetyAutomaton::from(&büchi);
        println!("deterministic: {}", safety.is_deterministic());
        let safety = safety.determinize();
        let safety = safety.minimize();

        let mut s = Vec::new();
        dot::render(&safety, &mut s).unwrap();
        let s = String::from_utf8(s).unwrap();
        println!("{s}");

        panic!();

        // target syntax:
        // let prop: Property<Observation> = property!(p, always ((p == Observation::B) -> next always (p != Observation::A)));
    }
}

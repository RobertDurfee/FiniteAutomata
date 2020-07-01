use std::collections::BTreeMap as Map;
use std::collections::BTreeSet as Set;
use std::rc::Rc;
use std::iter;

use crate::{StateIndex, TransitionIndex, ENFA, NFA, At, Slice, Contains, Insert};

pub struct DeterministicFiniteAutomaton<S, T> {
    state_to_index: Map<Rc<S>, StateIndex>,
    index_to_state: Map<StateIndex, Rc<S>>,
    transition_to_index: Map<StateIndex, Map<Rc<T>, (StateIndex, TransitionIndex)>>,
    index_to_transition: Map<TransitionIndex, (StateIndex, Rc<T>, StateIndex)>,
    transitions_from: Map<StateIndex, Set<TransitionIndex>>,
    initial: StateIndex,
    finals: Set<StateIndex>,
}

impl<S, T> DeterministicFiniteAutomaton<S, T> 
where
    S: Ord,
    T: Ord,
{
    pub fn new(initial: S) -> DeterministicFiniteAutomaton<S, T> {
        let initial_rc = Rc::new(initial);
        DeterministicFiniteAutomaton {
            state_to_index: map![initial_rc.clone() => 0.into()],
            index_to_state: map![0.into() => initial_rc],
            transition_to_index: Map::new(),
            index_to_transition: Map::new(),
            transitions_from: Map::new(),
            initial: 0.into(),
            finals: Set::new(),
        }
    }

    pub fn neighbor_indices_of<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.transition_indices_from(state_index).map(move |transition_index| self.index_to_transition.get(&transition_index).unwrap().2))
    }

    pub fn state_indices<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.index_to_state.keys().map(|&state_index| state_index))
    }

    pub fn transition_indices_from<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
        if self.index_to_state.get(&state_index).is_none() {
            panic!("state index out of bounds");
        }
        if let Some(transitions_from) = self.transitions_from.get(&state_index) {
            Box::new(transitions_from.iter().map(|&transition_index| transition_index))
        } else {
            Box::new(iter::empty())
        }
    }

    pub fn transition_indices<'a>(&'a self) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
        Box::new(self.index_to_transition.keys().map(|&transition_index| transition_index))
    }

    pub fn initial_index(&self) -> StateIndex {
        self.initial
    }

    pub fn set_final(&mut self, state_index: StateIndex) {
        self.at(state_index); // ensure state_index not out of bounds
        self.finals.insert(state_index);
    }

    pub fn is_final(&mut self, state_index: StateIndex) -> bool {
        self.at(state_index); // ensure state_index not out of bounds
        self.finals.contains(&state_index)
    }

    pub fn final_indices<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.finals.iter().map(|&ix| ix.into()))
    }
}

pub type DFA<S, T> = DeterministicFiniteAutomaton<S, T>;

impl<S, T> Insert<S, StateIndex> for DFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn insert(&mut self, state: S) -> StateIndex {
        if let Some(&state_index) = self.state_to_index.get(&state) {
            state_index
        } else {
            let state_index = self.state_to_index.len().into();
            let state_rc = Rc::new(state);
            self.state_to_index.insert(state_rc.clone(), state_index);
            self.index_to_state.insert(state_index, state_rc);
            state_index
        }
    }
}

impl<S, T> Insert<(StateIndex, T, StateIndex), TransitionIndex> for DFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn insert(&mut self, transition: (StateIndex, T, StateIndex)) -> TransitionIndex {
        let (source, transition, target) = transition;
        if self.index_to_state.get(&source).is_none() {
            panic!("source state index out of bounds");
        }
        if self.index_to_state.get(&target).is_none() {
            panic!("target state index out of bounds");
        }
        let transition_index = self.index_to_transition.len().into();
        let transition_rc = Rc::new(transition);
        if let Some(transitions) = self.transition_to_index.get_mut(&source) {
            if let Some(target_and_index) = transitions.get_mut(&transition_rc) {
                target_and_index.0 = target; // overwrite existing
                self.index_to_transition.get_mut(&target_and_index.1).unwrap().2 = target; // overwrite existing
                return target_and_index.1
            } else {
                transitions.insert(transition_rc.clone(), (target, transition_index));
            }
        } else {
            self.transition_to_index.insert(source, map![transition_rc.clone() => (target, transition_index)]);
        }
        self.index_to_transition.insert(transition_index, (source, transition_rc, target));
        if let Some(transitions_from) = self.transitions_from.get_mut(&source) {
            transitions_from.insert(transition_index);
        } else {
            self.transitions_from.insert(source, set![transition_index]);
        }
        transition_index
    }
}

impl<S, T> Contains<S, StateIndex> for DFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn contains(&self, state: &S) -> Option<StateIndex> {
        self.state_to_index.get(state).map(|&state_index| state_index)
    }
}

impl<S, T> Contains<(StateIndex, &T, StateIndex), TransitionIndex> for DFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn contains(&self, transition: &(StateIndex, &T, StateIndex)) -> Option<TransitionIndex> {
        let &(source, transition, target) = transition;
        if let Some(&target_and_index) = self.transition_to_index.get(&source).and_then(|transitions| transitions.get(transition)) {
            if target == target_and_index.0 {
                Some(target_and_index.1)
            } else {
                None
            }
        } else {
            None
        }
    }
}

impl<'a, S: 'a, T: 'a> At<'a, StateIndex> for DFA<S, T> {
    type Output = &'a S;

    fn at(&'a self, state_index: StateIndex) -> &'a S {
        self.index_to_state.get(&state_index).expect("state index out of bounds")
    }
}

impl<'a, S: 'a, T: 'a> At<'a, TransitionIndex> for DFA<S, T> {
    type Output = (StateIndex, &'a T, StateIndex);

    fn at(&'a self, transition_index: TransitionIndex) -> (StateIndex, &'a T, StateIndex) {
        let (source, transition, target) = self.index_to_transition.get(&transition_index).expect("transition index out of bounds");
        (*source, &*transition, *target)
    }
}

impl<'a, S, T> Slice<'a, StateIndex> for DFA<S, T> 
where
    S: Ord + 'a,
    T: Ord + 'a,
{
    type Output = &'a S;

    fn slice<I: IntoIterator<Item = StateIndex> + 'a>(&'a self, state_indices: I) -> Box<dyn Iterator<Item = &'a S> + 'a> {
        Box::new(state_indices.into_iter().map(move |state_index| self.at(state_index)))
    }
}

impl<'a, S, T> Slice<'a, TransitionIndex> for DFA<S, T> 
where
    S: Ord + 'a,
    T: Ord + 'a,
{
    type Output = (StateIndex, &'a T, StateIndex);

    fn slice<I: IntoIterator<Item = TransitionIndex> + 'a>(&'a self, transition_indices: I) -> Box<dyn Iterator<Item = (StateIndex, &'a T, StateIndex)> + 'a> {
        Box::new(transition_indices.into_iter().map(move |transition_index| self.at(transition_index)))
    }
}

impl<S, T> From<ENFA<S, T>> for DFA<Set<S>, T> 
where
    S: Ord,
    T: Ord,
{
    fn from(_enfa: ENFA<S, T>) -> DFA<Set<S>, T> {
        panic!("Not implemented")
    }
}

impl<S, T> From<NFA<S, T>> for DFA<Set<S>, T>
where
    S: Ord,
    T: Ord,
{
    fn from(_nfa: NFA<S, T>) -> DFA<Set<S>, T> {
        panic!("Not implemented")
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet as Set;
    use std::fmt::Debug;

    use crate::dfa::DFA;
    use crate::{At, Slice, Insert};

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, T, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Ord, T: Clone + Debug + Ord>(expected: Expected<S, T>, actual: DFA<S, T>) {
        assert_eq!(expected.initial, actual.at(actual.initial_index()).clone());
        assert_eq!(expected.transitions, actual.slice(actual.transition_indices()).map(|(source, transition, target)| (actual.at(source).clone(), transition.clone(), actual.at(target).clone())).collect());
        assert_eq!(expected.finals, actual.final_indices().map(|final_index| actual.at(final_index).clone()).collect());
    }

    #[test]
    fn test_1() {
        let expected = Expected::<_, char> {
            initial: set![0],
            transitions: set![],
            finals: set![set![1]]
        };
        let mut actual = DFA::new(set![0]);
        let s1 = actual.insert(set![1]);
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_2() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], 'a', set![1])
            ],
            finals: set![set![1]]
        };
        let mut actual = DFA::new(set![0]);
        let s0 = actual.initial_index();
        let s1 = actual.insert(set![1]);
        actual.insert((s0, 'a', s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_3() {
        let expected = Expected {
            initial: set![0, 1, 2, 3, 4],
            transitions: set![
                (set![0, 1, 2, 3, 4], 'a', set![1, 5])
            ],
            finals: set![set![0, 1, 2, 3, 4], set![1, 5]]
        };
        let mut actual = DFA::new(set![0, 1, 2, 3, 4]);
        let s01234 = actual.initial_index();
        let s15 = actual.insert(set![1, 5]);
        actual.insert((s01234, 'a', s15));
        actual.set_final(s01234);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_4() {
        let expected = Expected {
            initial: set![0, 2],
            transitions: set![
                (set![0, 2], 'a', set![1, 3, 4, 5])
            ],
            finals: set![set![1, 3, 4, 5]]
        };
        let mut actual = DFA::new(set![0, 2]);
        let s02 = actual.initial_index();
        let s1345 = actual.insert(set![1, 3, 4, 5]);
        actual.insert((s02, 'a', s1345));
        actual.set_final(s1345);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_5() {
        let expected = Expected {
            initial: set![0, 1, 2],
            transitions: set![
                (set![0, 1, 2], 'a', set![1, 2, 3]),
                (set![1, 2, 3], 'a', set![1, 2, 3])
            ],
            finals: set![set![0, 1, 2], set![1, 2, 3]]
        };
        let mut actual = DFA::new(set![0, 1, 2]);
        let s012 = actual.initial_index();
        let s123 = actual.insert(set![1, 2, 3]);
        actual.insert((s012, 'a', s123));
        actual.insert((s123, 'a', s123));
        actual.set_final(s012);
        actual.set_final(s123);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_6() {
        let expected = Expected {
            initial: set![0, 2, 4],
            transitions: set![
                (set![0, 2, 4], 'a', set![1, 5])
            ],
            finals: set![set![1, 3], set![1, 5]]
        };
        let mut actual = DFA::new(set![0, 2, 4]);
        let s024 = actual.initial_index();
        let s13 = actual.insert(set![1, 3]);
        let s15 = actual.insert(set![1, 5]);
        actual.insert((s024, 'a', s13));
        actual.insert((s024, 'a', s15)); // this will overwrite
        actual.set_final(s13);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }
}

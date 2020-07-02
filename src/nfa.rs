use std::collections::BTreeMap as Map;
use std::collections::BTreeSet as Set;
use std::rc::Rc;
use std::iter;

use crate::{StateIndex, TransitionIndex, ENFA, DFA, ContainsFrom, ContainsClosureFrom, At, Slice, Contains, Insert, Subsume};

#[derive(Clone)]
pub struct NondeterministicFiniteAutomaton<S, T> {
    state_to_index: Map<Rc<S>, StateIndex>,
    index_to_state: Map<StateIndex, Rc<S>>,
    transition_to_index: Map<StateIndex, Map<Rc<T>, Map<StateIndex, TransitionIndex>>>,
    index_to_transition: Map<TransitionIndex, (StateIndex, Rc<T>, StateIndex)>,
    transitions_from: Map<StateIndex, Set<TransitionIndex>>,
    initial: StateIndex,
    finals: Set<StateIndex>,
}

impl<S, T> NondeterministicFiniteAutomaton<S, T> 
where
    S: Ord,
    T: Ord,
{
    pub fn new(initial: S) -> NondeterministicFiniteAutomaton<S, T> {
        let initial_rc = Rc::new(initial);
        NondeterministicFiniteAutomaton {
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

    pub fn is_final(&self, state_index: StateIndex) -> bool {
        self.at(state_index); // ensure state_index not out of bounds
        self.finals.contains(&state_index)
    }

    pub fn final_indices<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.finals.iter().map(|&ix| ix.into()))
    }
}

pub type NFA<S, T> = NondeterministicFiniteAutomaton<S, T>;

impl<S, T> Insert<S, StateIndex> for NFA<S, T>
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

impl<S, T> Insert<(StateIndex, T, StateIndex), TransitionIndex> for NFA<S, T>
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
            if let Some(targets) = transitions.get_mut(&transition_rc) {
                targets.insert(target, transition_index);
            } else {
                transitions.insert(transition_rc.clone(), map![target => transition_index]);
            }
        } else {
            self.transition_to_index.insert(source, map![transition_rc.clone() => map![target => transition_index]]);
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

impl<S, T> Contains<S, StateIndex> for NFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn contains(&self, state: &S) -> Option<StateIndex> {
        self.state_to_index.get(state).map(|&state_index| state_index)
    }
}

impl<S, T> Contains<(StateIndex, &T, StateIndex), TransitionIndex> for NFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn contains(&self, transition: &(StateIndex, &T, StateIndex)) -> Option<TransitionIndex> {
        let &(source, transition, target) = transition;
        self.transition_to_index.get(&source).and_then(|transitions| transitions.get(transition).and_then(|targets| targets.get(&target).map(|&target| target)))
    }
}

impl<'a, S: 'a, T: 'a> At<'a, StateIndex> for NFA<S, T> {
    type Output = &'a S;

    fn at(&'a self, state_index: StateIndex) -> &'a S {
        self.index_to_state.get(&state_index).expect("state index out of bounds")
    }
}

impl<'a, S: 'a, T: 'a> At<'a, TransitionIndex> for NFA<S, T> {
    type Output = (StateIndex, &'a T, StateIndex);

    fn at(&'a self, transition_index: TransitionIndex) -> (StateIndex, &'a T, StateIndex) {
        let (source, transition, target) = self.index_to_transition.get(&transition_index).expect("transition index out of bounds");
        (*source, &*transition, *target)
    }
}

impl<'a, S, T> Slice<'a, StateIndex> for NFA<S, T> 
where
    S: Ord + 'a,
    T: Ord + 'a,
{
    type Output = &'a S;

    fn slice<I: IntoIterator<Item = StateIndex> + 'a>(&'a self, state_indices: I) -> Box<dyn Iterator<Item = &'a S> + 'a> {
        Box::new(state_indices.into_iter().map(move |state_index| self.at(state_index)))
    }
}

impl<'a, S, T> Slice<'a, TransitionIndex> for NFA<S, T> 
where
    S: Ord + 'a,
    T: Ord + 'a,
{
    type Output = (StateIndex, &'a T, StateIndex);

    fn slice<I: IntoIterator<Item = TransitionIndex> + 'a>(&'a self, transition_indices: I) -> Box<dyn Iterator<Item = (StateIndex, &'a T, StateIndex)> + 'a> {
        Box::new(transition_indices.into_iter().map(move |transition_index| self.at(transition_index)))
    }
}

impl<'a, S, T> Slice<'a, &'a StateIndex> for NFA<S, T> 
where
    S: Ord + 'a,
    T: Ord + 'a,
{
    type Output = &'a S;

    fn slice<I: IntoIterator<Item = &'a StateIndex> + 'a>(&'a self, state_indices: I) -> Box<dyn Iterator<Item = &'a S> + 'a> {
        Box::new(state_indices.into_iter().map(move |&state_index| self.at(state_index)))
    }
}

impl<'a, S, T> Slice<'a, &'a TransitionIndex> for NFA<S, T> 
where
    S: Ord + 'a,
    T: Ord + 'a,
{
    type Output = (StateIndex, &'a T, StateIndex);

    fn slice<I: IntoIterator<Item = &'a TransitionIndex> + 'a>(&'a self, transition_indices: I) -> Box<dyn Iterator<Item = (StateIndex, &'a T, StateIndex)> + 'a> {
        Box::new(transition_indices.into_iter().map(move |&transition_index| self.at(transition_index)))
    }
}

impl<S, T> ContainsFrom<ENFA<S, T>, StateIndex> for NFA<S, T> 
where
    S: Ord,
    T: Ord,
{
    fn contains_from(&self, from: &ENFA<S, T>, state_index: StateIndex) -> Option<StateIndex> {
        self.contains(from.at(state_index))
    }
}

impl<S, T> ContainsFrom<NFA<S, T>, StateIndex> for NFA<S, T> 
where
    S: Ord,
    T: Ord,
{
    fn contains_from(&self, from: &NFA<S, T>, state_index: StateIndex) -> Option<StateIndex> {
        self.contains(from.at(state_index))
    }
}

impl<S, T> ContainsFrom<DFA<S, T>, StateIndex> for NFA<S, T> 
where
    S: Ord,
    T: Ord,
{
    fn contains_from(&self, from: &DFA<S, T>, state_index: StateIndex) -> Option<StateIndex> {
        self.contains(from.at(state_index))
    }
}

impl<'a, S, T> ContainsClosureFrom<'a, ENFA<S, T>, StateIndex> for NFA<Set<S>, T>
where
    S: Clone + Ord + 'a,
    T: Clone + Ord + 'a,
{
    fn contains_closure_from<I: IntoIterator<Item = &'a StateIndex> + 'a>(&'a self, from: &'a ENFA<S, T>, state_indices: I) -> Option<StateIndex> {
        self.contains(&from.slice(state_indices).cloned().collect()) // TODO: this should be possible without cloning
    }
}

impl<'a, S, T> ContainsClosureFrom<'a, NFA<S, T>, StateIndex> for NFA<Set<S>, T>
where
    S: Clone + Ord + 'a,
    T: Clone + Ord + 'a,
{
    fn contains_closure_from<I: IntoIterator<Item = &'a StateIndex> + 'a>(&'a self, from: &'a NFA<S, T>, state_indices: I) -> Option<StateIndex> {
        self.contains(&from.slice(state_indices).cloned().collect()) // TODO: this should be possible without cloning
    }
}

impl<'a, S, T> ContainsClosureFrom<'a, DFA<S, T>, StateIndex> for NFA<Set<S>, T>
where
    S: Clone + Ord + 'a,
    T: Clone + Ord + 'a,
{
    fn contains_closure_from<I: IntoIterator<Item = &'a StateIndex> + 'a>(&'a self, from: &'a DFA<S, T>, state_indices: I) -> Option<StateIndex> {
        self.contains(&from.slice(state_indices).cloned().collect()) // TODO: this should be possible without cloning
    }
}

impl<S, T> From<ENFA<S, T>> for NFA<Set<S>, T> 
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn from(enfa: ENFA<S, T>) -> NFA<Set<S>, T> {
        let initial_closure_indices: Set<StateIndex> = enfa.closure_indices(enfa.initial_index()).collect();
        let initial_closure = enfa.slice(&initial_closure_indices).cloned().collect();
        let mut stack = vec![initial_closure_indices];
        let mut nfa = NFA::new(initial_closure);
        while let Some(source_closure_indices) = stack.pop() {
            let source_index = nfa.contains_closure_from(&enfa, &source_closure_indices).expect("closure does not exist");
            for &source_closure_index in &source_closure_indices {
                if enfa.is_final(source_closure_index) {
                    nfa.set_final(source_index);
                }
                for transition_index in enfa.transition_indices_from(source_closure_index) {
                    let (_, transition, target_index) = enfa.at(transition_index);
                    if let Some(transition) = transition {
                        let target_closure_indices = enfa.closure_indices(target_index).collect();
                        if let Some(target_index) = nfa.contains_closure_from(&enfa, &target_closure_indices) {
                            nfa.insert((source_index, transition.clone(), target_index));
                        } else {
                            let target_closure = enfa.slice(&target_closure_indices).cloned().collect();
                            stack.push(target_closure_indices);
                            let target_index = nfa.insert(target_closure);
                            nfa.insert((source_index, transition.clone(), target_index));
                        }
                    }
                }
            }
        }
        nfa
    }
}

impl<S, T> From<DFA<S, T>> for NFA<S, T> 
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn from(dfa: DFA<S, T>) -> NFA<S, T> {
        let initial = dfa.at(dfa.initial_index());
        let mut nfa = NFA::new(initial.clone());
        for state_index in dfa.state_indices() {
            let state = dfa.at(state_index);
            nfa.insert(state.clone());
        }
        for transition_index in dfa.transition_indices() {
            let (source_index, transition, target_index) = dfa.at(transition_index);
            let source_index = nfa.contains_from(&dfa, source_index).expect("state does not exist");
            let target_index = nfa.contains_from(&dfa, target_index).expect("state does not exist");
            nfa.insert((source_index, transition.clone(), target_index));
        }
        for final_index in dfa.final_indices() {
            let final_index = nfa.contains_from(&dfa, final_index).expect("state does not exist");
            nfa.set_final(final_index);
        }
        nfa
    }
}

impl<S, T> Subsume<ENFA<S, T>> for NFA<Set<S>, T> 
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn subsume(&mut self, enfa: &ENFA<S, T>) {
        let initial_closure_indices: Set<StateIndex> = enfa.closure_indices(enfa.initial_index()).collect();
        let initial_closure: Set<S> = enfa.slice(&initial_closure_indices).cloned().collect();
        let mut stack = vec![initial_closure_indices];
        self.insert(initial_closure);
        while let Some(source_closure_indices) = stack.pop() {
            let source_index = self.contains_closure_from(enfa, &source_closure_indices).expect("closure does not exist");
            for &source_closure_index in &source_closure_indices {
                for transition_index in enfa.transition_indices_from(source_closure_index) {
                    let (_, transition, target_index) = enfa.at(transition_index);
                    if let Some(transition) = transition {
                        let target_closure_indices = enfa.closure_indices(target_index).collect();
                        if let Some(target_index) = self.contains_closure_from(enfa, &target_closure_indices) {
                            self.insert((source_index, transition.clone(), target_index));
                        } else {
                            let target_closure = enfa.slice(&target_closure_indices).cloned().collect();
                            stack.push(target_closure_indices);
                            let target_index = self.insert(target_closure);
                            self.insert((source_index, transition.clone(), target_index));
                        }
                    }
                }
            }
        }
    }
}

impl<S, T> Subsume<NFA<S, T>> for NFA<S, T> 
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn subsume(&mut self, nfa: &NFA<S, T>) {
        for state_index in nfa.state_indices() {
            let state = nfa.at(state_index);
            self.insert(state.clone());
        }
        for transition_index in nfa.transition_indices() {
            let (source_index, transition, target_index) = nfa.at(transition_index);
            let source_index = self.contains_from(nfa, source_index).expect("state does not exist");
            let target_index = self.contains_from(nfa, target_index).expect("state does not exist");
            self.insert((source_index, transition.clone(), target_index));
        }
    }
}

impl<S, T> Subsume<DFA<S, T>> for NFA<S, T> 
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn subsume(&mut self, dfa: &DFA<S, T>) {
        for state_index in dfa.state_indices() {
            let state = dfa.at(state_index);
            self.insert(state.clone());
        }
        for transition_index in dfa.transition_indices() {
            let (source_index, transition, target_index) = dfa.at(transition_index);
            let source_index = self.contains_from(dfa, source_index).expect("state does not exist");
            let target_index = self.contains_from(dfa, target_index).expect("state does not exist");
            self.insert((source_index, transition.clone(), target_index));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet as Set;
    use std::fmt::Debug;

    use crate::{At, Slice, Insert};
    use crate::nfa::NFA;
    use crate::enfa::ENFA;

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, T, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Ord, T: Clone + Debug + Ord>(expected: Expected<S, T>, actual: NFA<S, T>) {
        assert_eq!(expected.initial, actual.at(actual.initial_index()).clone());
        assert_eq!(expected.transitions, actual.slice(actual.transition_indices()).map(|(source, transition, target)| (actual.at(source).clone(), transition.clone(), actual.at(target).clone())).collect());
        assert_eq!(expected.finals, actual.final_indices().map(|final_index| actual.at(final_index).clone()).collect());
    }

    #[test]
    fn test_1() {
        let expected = Expected::<_, char> {
            initial: set![0, 1],
            transitions: set![],
            finals: set![set![0, 1]]
        };
        let mut actual = NFA::new(set![0, 1]);
        let s0 = actual.initial_index();
        actual.set_final(s0);
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
        let mut actual = NFA::new(set![0]);
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
        let mut actual = NFA::new(set![0, 1, 2, 3, 4]);
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
        let mut actual = NFA::new(set![0, 2]);
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
        let mut actual = NFA::new(set![0, 1, 2]);
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
                (set![0, 2, 4], 'a', set![1, 3]),
                (set![0, 2, 4], 'a', set![1, 5])
            ],
            finals: set![set![1, 3], set![1, 5]]
        };
        let mut actual = NFA::new(set![0, 2, 4]);
        let s024 = actual.initial_index();
        let s13 = actual.insert(set![1, 3]);
        let s15 = actual.insert(set![1, 5]);
        actual.insert((s024, 'a', s13));
        actual.insert((s024, 'a', s15));
        actual.set_final(s13);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_7() {
        let expected = Expected::<_, char> {
            initial: set![0, 1],
            transitions: set![],
            finals: set![set![0, 1]]
        };
        let mut enfa = ENFA::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.insert(1);
        enfa.insert((s0, None, s1));
        enfa.set_final(s1);
        let actual = NFA::from(enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_8() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], 'a', set![1])
            ],
            finals: set![set![1]]
        };
        let mut enfa = ENFA::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.insert(1);
        enfa.insert((s0, Some('a'), s1));
        enfa.set_final(s1);
        let actual = NFA::from(enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_9() {
        let expected = Expected {
            initial: set![0, 1, 2, 3, 4],
            transitions: set![
                (set![0, 1, 2, 3, 4], 'a', set![1, 5])
            ],
            finals: set![set![0, 1, 2, 3, 4], set![1, 5]]
        };
        let mut enfa = ENFA::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.insert(1);
        let s2 = enfa.insert(2);
        let s3 = enfa.insert(3);
        let s4 = enfa.insert(4);
        let s5 = enfa.insert(5);
        enfa.insert((s0, None,      s2));
        enfa.insert((s0, None,      s4));
        enfa.insert((s2, None,      s3));
        enfa.insert((s4, Some('a'), s5));
        enfa.insert((s3, None,      s1));
        enfa.insert((s5, None,      s1));
        enfa.set_final(s1);
        let actual = NFA::from(enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_10() {
        let expected = Expected {
            initial: set![0, 2],
            transitions: set![
                (set![0, 2], 'a', set![1, 3, 4, 5])
            ],
            finals: set![set![1, 3, 4, 5]]
        };
        let mut enfa = ENFA::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.insert(1);
        let s2 = enfa.insert(2);
        let s3 = enfa.insert(3);
        let s4 = enfa.insert(4);
        let s5 = enfa.insert(5);
        enfa.insert((s0, None,      s2));
        enfa.insert((s2, Some('a'), s3));
        enfa.insert((s3, None,      s4));
        enfa.insert((s4, None,      s5));
        enfa.insert((s5, None,      s1));
        enfa.set_final(s1);
        let actual = NFA::from(enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_11() {
        let expected = Expected {
            initial: set![0, 1, 2],
            transitions: set![
                (set![0, 1, 2], 'a', set![1, 2, 3]),
                (set![1, 2, 3], 'a', set![1, 2, 3])
            ],
            finals: set![set![0, 1, 2], set![1, 2, 3]]
        };
        let mut enfa = ENFA::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.insert(1);
        let s2 = enfa.insert(2);
        let s3 = enfa.insert(3);
        enfa.insert((s0, None,      s1));
        enfa.insert((s0, None,      s2));
        enfa.insert((s2, Some('a'), s3));
        enfa.insert((s3, None,      s2));
        enfa.insert((s3, None,      s1));
        enfa.set_final(s1);
        let actual = NFA::from(enfa);
        assert_eq(expected, actual);
    }
}

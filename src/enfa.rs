use std::collections::BTreeSet as Set;

use crate::{At, StateIndex, NFA, DFA, ContainsFrom, ContainsClosureFrom, ContainsAllFrom, Contains, Insert, Slice, Subsume};

pub type EpsilonNondeterministicFiniteAutomaton<S, T> = NFA<S, Option<T>>;

pub type ENFA<S, T> = EpsilonNondeterministicFiniteAutomaton<S, T>;

// impl<S, T> ContainsFrom<ENFA<S, T>, StateIndex> for ENFA<S, T> is implicit in nfa.rs

impl<S, T> ContainsFrom<NFA<S, T>, StateIndex> for ENFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn contains_from(&self, from: &NFA<S, T>, state_index: StateIndex) -> Option<StateIndex> {
        self.contains(from.at(state_index))
    }
}

impl<S, T> ContainsFrom<DFA<S, T>, StateIndex> for ENFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn contains_from(&self, from: &DFA<S, T>, state_index: StateIndex) -> Option<StateIndex> {
        self.contains(from.at(state_index))
    }
}

// impl<'a, S, T> ContainsClosureFrom<'a, ENFA<S, T>, StateIndex> for ENFA<Set<S>, T> is implicit in nfa.rs

impl<'a, S, T> ContainsClosureFrom<'a, NFA<S, T>, StateIndex> for ENFA<Set<S>, T>
where
    S: Clone + Ord + 'a,
    T: Clone + Ord + 'a,
{
    fn contains_closure_from<I: IntoIterator<Item = &'a StateIndex> + 'a>(&'a self, from: &'a NFA<S, T>, state_indices: I) -> Option<StateIndex> {
        self.contains(&from.slice(state_indices).cloned().collect()) // TODO: this should be possible without cloning
    }
}

impl<'a, S, T> ContainsClosureFrom<'a, DFA<S, T>, StateIndex> for ENFA<Set<S>, T>
where
    S: Clone + Ord + 'a,
    T: Clone + Ord + 'a,
{
    fn contains_closure_from<I: IntoIterator<Item = &'a StateIndex> + 'a>(&'a self, from: &'a DFA<S, T>, state_indices: I) -> Option<StateIndex> {
        self.contains(&from.slice(state_indices).cloned().collect()) // TODO: this should be possible without cloning
    }
}

// impl<'a, S, T> ContainsAllFrom<'a, ENFA<S, T>, StateIndex> for ENFA<S, T> is implicit in nfa.rs

impl<'a, S, T> ContainsAllFrom<'a, NFA<S, T>, StateIndex> for ENFA<S, T>
where
    S: Ord + 'a,
    T: Ord + 'a,
{
    fn contains_all_from<I: IntoIterator<Item = &'a StateIndex> + 'a>(&'a self, from: &'a NFA<S, T>, state_indices: I) -> Option<Box<dyn Iterator<Item = StateIndex> + 'a>> {
        from.slice(state_indices).map(|state| self.contains(state)).collect::<Option<Set<_>>>().map(|state_indices| Box::new(state_indices.into_iter()) as Box<dyn Iterator<Item = StateIndex>>)
    }
}

impl<'a, S, T> ContainsAllFrom<'a, DFA<S, T>, StateIndex> for ENFA<S, T>
where
    S: Ord + 'a,
    T: Ord + 'a,
{
    fn contains_all_from<I: IntoIterator<Item = &'a StateIndex> + 'a>(&'a self, from: &'a DFA<S, T>, state_indices: I) -> Option<Box<dyn Iterator<Item = StateIndex> + 'a>> {
        from.slice(state_indices).map(|state| self.contains(state)).collect::<Option<Set<_>>>().map(|state_indices| Box::new(state_indices.into_iter()) as Box<dyn Iterator<Item = StateIndex>>)
    }
}

impl<S, T> ENFA<S, T> 
where
    S: Ord,
    T: Ord,
{
    pub fn closure_indices<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        let mut stack = vec![state_index];
        let mut closure = Set::new();
        while let Some(source_state_index) = stack.pop() {
            closure.insert(source_state_index);
            for transition_index in self.transition_indices_from(source_state_index) {
                let (_, transition, target_index) = self.at(transition_index);
                if transition.is_none() && !closure.contains(&target_index) {
                    stack.push(target_index);
                }
            }
        }
        Box::new(closure.into_iter())
    }
}

impl<S, T> From<NFA<S, T>> for ENFA<S, T>
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn from(nfa: NFA<S, T>) -> ENFA<S, T> {
        let initial = nfa.at(nfa.initial_index());
        let mut enfa = ENFA::new(initial.clone());
        for state_index in nfa.state_indices() {
            let state = nfa.at(state_index);
            enfa.insert(state.clone());
        }
        for transition_index in nfa.transition_indices() {
            let (source_index, transition, target_index) = nfa.at(transition_index);
            let source_index = enfa.contains_from(&nfa, source_index).expect("state does not exist");
            let target_index = enfa.contains_from(&nfa, target_index).expect("state does not exist");
            enfa.insert((source_index, Some(transition.clone()), target_index));
        }
        for final_index in nfa.final_indices() {
            let final_index = enfa.contains_from(&nfa, final_index).expect("state does not exist");
            enfa.set_final(final_index);
        }
        enfa
    }
}

impl<S, T> From<DFA<S, T>> for ENFA<S, T>
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn from(dfa: DFA<S, T>) -> ENFA<S, T> {
        let initial = dfa.at(dfa.initial_index());
        let mut enfa = ENFA::new(initial.clone());
        for state_index in dfa.state_indices() {
            let state = dfa.at(state_index);
            enfa.insert(state.clone());
        }
        for transition_index in dfa.transition_indices() {
            let (source_index, transition, target_index) = dfa.at(transition_index);
            let source_index = enfa.contains_from(&dfa, source_index).expect("state does not exist");
            let target_index = enfa.contains_from(&dfa, target_index).expect("state does not exist");
            enfa.insert((source_index, Some(transition.clone()), target_index));
        }
        for final_index in dfa.final_indices() {
            let final_index = enfa.contains_from(&dfa, final_index).expect("state does not exist");
            enfa.set_final(final_index);
        }
        enfa
    }
}

// impl<S, T> Subsume<ENFA<S, T>> for ENFA<S, T> is implicit in nfa.rs

impl<S, T> Subsume<NFA<S, T>> for ENFA<S, T> 
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
            self.insert((source_index, Some(transition.clone()), target_index));
        }
    }
}

impl<S, T> Subsume<DFA<S, T>> for ENFA<S, T> 
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
            self.insert((source_index, Some(transition.clone()), target_index));
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet as Set;
    use std::fmt::Debug;

    use crate::enfa::ENFA;
    use crate::{At, Slice, Insert};

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, Option<T>, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Ord, T: Clone + Debug + Ord>(expected: Expected<S, T>, actual: ENFA<S, T>) {
        assert_eq!(expected.initial, actual.at(actual.initial_index()).clone());
        assert_eq!(expected.transitions, actual.slice(actual.transition_indices()).map(|(source, transition, target)| (actual.at(source).clone(), transition.clone(), actual.at(target).clone())).collect());
        assert_eq!(expected.finals, actual.final_indices().map(|final_index| actual.at(final_index).clone()).collect());
    }

    #[test]
    fn test_1() {
        let expected = Expected::<_, char> {
            initial: 0,
            transitions: set![
                (0, None, 1)
            ],
            finals: set![1]
        };
        let mut actual = ENFA::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.insert(1);
        actual.insert((s0, None, s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_2() {
        let expected = Expected {
            initial: 0,
            transitions: set![
                (0, Some('a'), 1)
            ],
            finals: set![1]
        };
        let mut actual = ENFA::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.insert(1);
        actual.insert((s0, Some('a'), s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_3() {
        let expected = Expected {
            initial: 0,
            transitions: set![
                (0, None,      2),
                (0, None,      4),
                (2, None,      3),
                (4, Some('a'), 5),
                (3, None,      1),
                (5, None,      1)
            ],
            finals: set![1]
        };
        let mut actual = ENFA::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.insert(1);
        let s2 = actual.insert(2);
        let s3 = actual.insert(3);
        let s4 = actual.insert(4);
        let s5 = actual.insert(5);
        actual.insert((s0, None,      s2));
        actual.insert((s0, None,      s4));
        actual.insert((s2, None,      s3));
        actual.insert((s4, Some('a'), s5));
        actual.insert((s3, None,      s1));
        actual.insert((s5, None,      s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_4() {
        let expected = Expected {
            initial: 0,
            transitions: set![
                (0, None,      2),
                (2, Some('a'), 3),
                (3, None,      4),
                (4, None,      5),
                (5, None,      1)
            ],
            finals: set![1]
        };
        let mut actual = ENFA::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.insert(1);
        let s2 = actual.insert(2);
        let s3 = actual.insert(3);
        let s4 = actual.insert(4);
        let s5 = actual.insert(5);
        actual.insert((s0, None,      s2));
        actual.insert((s2, Some('a'), s3));
        actual.insert((s3, None,      s4));
        actual.insert((s4, None,      s5));
        actual.insert((s5, None,      s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_5() {
        let expected = Expected {
            initial: 0,
            transitions: set![
                (0, None,      1),
                (0, None,      2),
                (2, Some('a'), 3),
                (3, None,      2),
                (3, None,      1)
            ],
            finals: set![1]
        };
        let mut actual = ENFA::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.insert(1);
        let s2 = actual.insert(2);
        let s3 = actual.insert(3);
        actual.insert((s0, None,      s1));
        actual.insert((s0, None,      s2));
        actual.insert((s2, Some('a'), s3));
        actual.insert((s3, None,      s2));
        actual.insert((s3, None,      s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }
}

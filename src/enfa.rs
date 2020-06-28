use std::collections::BTreeSet as Set;

use crate::{StateIndex, NFA, DFA, TranslateFrom};

pub type EpsilonNondeterministicFiniteAutomaton<S, T> = NFA<S, Option<T>>;

pub type ENFA<S, T> = EpsilonNondeterministicFiniteAutomaton<S, T>;

impl<S, T> TranslateFrom<NFA<S, T>> for ENFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn translate_from(&self, from: &NFA<S, T>, state_index: StateIndex) -> StateIndex {
        self.contains_state(from.state(state_index)).expect("state does not exist")
    }
}

impl<S, T> TranslateFrom<DFA<S, T>> for ENFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn translate_from(&self, from: &DFA<S, T>, state_index: StateIndex) -> StateIndex {
        self.contains_state(from.state(state_index)).expect("state does not exist")
    }
}

impl<S, T> ENFA<S, T> 
where
    S: Ord,
    T: Ord,
{
    pub fn get_closure<'a>(&'a self, state_index: StateIndex) -> Set<StateIndex> {
        let mut stack = vec![state_index];
        let mut closure = Set::new();
        while let Some(source_state_index) = stack.pop() {
            closure.insert(source_state_index);
            for transition_index in self.transitions_from(source_state_index) {
                let (_, transition, target_index) = self.transition(transition_index);
                if transition.is_none() && !closure.contains(&target_index) {
                    stack.push(target_index);
                }
            }
        }
        closure
    }
}

impl<S, T> From<NFA<S, T>> for ENFA<S, T>
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn from(nfa: NFA<S, T>) -> ENFA<S, T> {
        let initial_index = nfa.initial();
        let initial = nfa.state(initial_index);
        let mut enfa = ENFA::new(initial.clone());
        for state_index in nfa.states() {
            let state = nfa.state(state_index);
            enfa.insert_state(state.clone());
        }
        for transition_index in nfa.transitions() {
            let (source_index, transition, target_index) = nfa.transition(transition_index);
            let source_index = enfa.translate_from(&nfa, source_index);
            let target_index = enfa.translate_from(&nfa, target_index);
            enfa.insert_transition(source_index, Some(transition.clone()), target_index);
        }
        for final_index in nfa.finals() {
            let final_index = enfa.translate_from(&nfa, final_index);
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
        let initial_index = dfa.initial();
        let initial = dfa.state(initial_index);
        let mut enfa = ENFA::new(initial.clone());
        for state_index in dfa.states() {
            let state = dfa.state(state_index);
            enfa.insert_state(state.clone());
        }
        for transition_index in dfa.transitions() {
            let (source_index, transition, target_index) = dfa.transition(transition_index);
            let source_index = enfa.translate_from(&dfa, source_index);
            let target_index = enfa.translate_from(&dfa, target_index);
            enfa.insert_transition(source_index, Some(transition.clone()), target_index);
        }
        for final_index in dfa.finals() {
            let final_index = enfa.translate_from(&dfa, final_index);
            enfa.set_final(final_index);
        }
        enfa
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet as Set;
    use std::fmt::Debug;

    use crate::enfa::ENFA;

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, Option<T>, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Ord, T: Clone + Debug + Ord>(expected: Expected<S, T>, actual: ENFA<S, T>) {
        assert_eq!(expected.initial, actual.state(actual.initial()).clone());
        assert_eq!(expected.transitions, actual.transitions().map(|transition_index| actual.transition(transition_index)).map(|(source, transition, target)| (actual.state(source).clone(), transition.clone(), actual.state(target).clone())).collect());
        assert_eq!(expected.finals, actual.finals().map(|final_index| actual.state(final_index).clone()).collect());
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
        let s0 = actual.initial();
        let s1 = actual.insert_state(1);
        actual.insert_transition(s0, None, s1);
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
        let s0 = actual.initial();
        let s1 = actual.insert_state(1);
        actual.insert_transition(s0, Some('a'), s1);
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
        let s0 = actual.initial();
        let s1 = actual.insert_state(1);
        let s2 = actual.insert_state(2);
        let s3 = actual.insert_state(3);
        let s4 = actual.insert_state(4);
        let s5 = actual.insert_state(5);
        actual.insert_transition(s0, None,      s2);
        actual.insert_transition(s0, None,      s4);
        actual.insert_transition(s2, None,      s3);
        actual.insert_transition(s4, Some('a'), s5);
        actual.insert_transition(s3, None,      s1);
        actual.insert_transition(s5, None,      s1);
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
        let s0 = actual.initial();
        let s1 = actual.insert_state(1);
        let s2 = actual.insert_state(2);
        let s3 = actual.insert_state(3);
        let s4 = actual.insert_state(4);
        let s5 = actual.insert_state(5);
        actual.insert_transition(s0, None,      s2);
        actual.insert_transition(s2, Some('a'), s3);
        actual.insert_transition(s3, None,      s4);
        actual.insert_transition(s4, None,      s5);
        actual.insert_transition(s5, None,      s1);
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
        let s0 = actual.initial();
        let s1 = actual.insert_state(1);
        let s2 = actual.insert_state(2);
        let s3 = actual.insert_state(3);
        actual.insert_transition(s0, None,      s1);
        actual.insert_transition(s0, None,      s2);
        actual.insert_transition(s2, Some('a'), s3);
        actual.insert_transition(s3, None,      s2);
        actual.insert_transition(s3, None,      s1);
        actual.set_final(s1);
        assert_eq(expected, actual);
    }
}

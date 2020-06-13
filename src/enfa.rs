use crate::{StateIndex, NFA, DFA};

pub type EpsilonNondeterministicFiniteAutomaton<S, T> = NFA<S, Option<T>>;

pub type ENFA<S, T> = EpsilonNondeterministicFiniteAutomaton<S, T>;

impl<S, T> ENFA<S, T> 
where
    S: Ord,
    T: Ord,
{
    pub fn get_closure<'a>(&'a self, _state_index: StateIndex) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        panic!("Not implemented")
    }
}

impl<S, T> From<NFA<S, T>> for ENFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn from(_nfa: NFA<S, T>) -> ENFA<S, T> {
        panic!("Not implemented")
    }
}

impl<S, T> From<DFA<S, T>> for ENFA<S, T>
where
    S: Ord,
    T: Ord,
{
    fn from(_dfa: DFA<S, T>) -> ENFA<S, T> {
        panic!("Not implemented")
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
        assert_eq!(expected.initial, actual.get_state(actual.get_initial()).clone());
        assert_eq!(expected.transitions, actual.transitions().map(|transition_index| actual.get_transition(transition_index)).map(|(source, transition, target)| (actual.get_state(source).clone(), transition.clone(), actual.get_state(target).clone())).collect());
        assert_eq!(expected.finals, actual.finals().map(|final_index| actual.get_state(final_index).clone()).collect());
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
        let s0 = actual.get_initial();
        let s1 = actual.add_state(1);
        actual.add_transition(s0, None, s1);
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
        let s0 = actual.get_initial();
        let s1 = actual.add_state(1);
        actual.add_transition(s0, Some('a'), s1);
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
        let s0 = actual.get_initial();
        let s1 = actual.add_state(1);
        let s2 = actual.add_state(2);
        let s3 = actual.add_state(3);
        let s4 = actual.add_state(4);
        let s5 = actual.add_state(5);
        actual.add_transition(s0, None,      s2);
        actual.add_transition(s0, None,      s4);
        actual.add_transition(s2, None,      s3);
        actual.add_transition(s4, Some('a'), s5);
        actual.add_transition(s3, None,      s1);
        actual.add_transition(s5, None,      s1);
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
        let s0 = actual.get_initial();
        let s1 = actual.add_state(1);
        let s2 = actual.add_state(2);
        let s3 = actual.add_state(3);
        let s4 = actual.add_state(4);
        let s5 = actual.add_state(5);
        actual.add_transition(s0, None,      s2);
        actual.add_transition(s2, Some('a'), s3);
        actual.add_transition(s3, None,      s4);
        actual.add_transition(s4, None,      s5);
        actual.add_transition(s5, None,      s1);
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
        let s0 = actual.get_initial();
        let s1 = actual.add_state(1);
        let s2 = actual.add_state(2);
        let s3 = actual.add_state(3);
        actual.add_transition(s0, None,      s1);
        actual.add_transition(s0, None,      s2);
        actual.add_transition(s2, Some('a'), s3);
        actual.add_transition(s3, None,      s2);
        actual.add_transition(s3, None,      s1);
        actual.set_final(s1);
        assert_eq(expected, actual);
    }
}

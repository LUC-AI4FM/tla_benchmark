---------------- MODULE StateMachine ----------------

EXTENDS Integers

VARIABLES x

\* @type: (Set(a), a -> Bool, (a, b) -> Bool) -> Set(a);
\* A higher-order helper operator that filters a set S using two
\* operator arguments, P and Q. It returns a subset of S
\* containing elements s for which P(s) and Q(s, TRUE) are both true.
Op(S, P(_), Q(_, _)) == {s \in S : P(s) /\ Q(s, TRUE)}

\* Filter predicate: returns TRUE if n is greater than 1.
IsGreaterThanOne(n) == n > 1

\* Filter predicate: returns TRUE if n is odd. The second argument is ignored.
IsOdd(n, b) == (n % 2 = 1)

\* The initial state constrains x to belong to the subset of {1,2,3,4,5}
\* consisting of elements that are both greater than 1 and odd.
Init ==
    LET S == {1, 2, 3, 4, 5}
    IN x \in Op(S, IsGreaterThanOne, IsOdd)

\* The only possible step is a stuttering step.
Next ==
    UNCHANGED x

\* The full specification.
Spec == Init /\ [][Next]_x

=====================================================
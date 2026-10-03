---- MODULE TemporalSystem ----
EXTENDS Integers

VARIABLES s

\* The predicate F(var) holds when its argument is an even integer in 0..9.
F(var) == (var \in 0..9) /\ (var % 2 = 0)

\* Initially, s is 0.
Init == s = 0

\* The next-state relation requires that for any step, either the new value of s
\* satisfies the predicate F, or s stutters. This is equivalent to the formula [F(s')]_s.
Next == F(s') \/ (s' = s)

\* The full specification is that s is initially 0, and every step satisfies the Next relation.
\* This is equivalent to Init /\ [][F(s')]_s.
Spec == Init /\ [][Next]_s

=============================================================================
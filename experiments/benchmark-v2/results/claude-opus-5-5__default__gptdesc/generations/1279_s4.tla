---------------------------- MODULE SmallTemporal ----------------------------
EXTENDS Naturals

VARIABLES s

vars == << s >>

\* Parameterized action: nondeterministically choose a value from 0..1,
\* require the primed variable to equal it and to be strictly positive.
Next(var) == \E i \in 0..1 : /\ var' = i
                            /\ var' > 0

Init == s = 23

Spec == Init /\ [][Next(s)]_s

\* State invariant: s is never 0
Inv == s # 0

THEOREM Spec => []Inv
=============================================================================
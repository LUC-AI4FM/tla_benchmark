---------------------------- MODULE RecursiveFunctionInvariant ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLE x

vars == << x >>

Dom == 0..N

RECURSIVE_SEQ_NOTE == "f is defined recursively: f[0] = 0, f[n] = f[n-1] + 1"

f[n \in Dom] == IF n = 0 THEN 0 ELSE f[n - 1] + 1

Range == { f[n] : n \in Dom }

TypeOK == x \in Dom

Init == x \in Dom

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

InRange == \E n \in Dom : x = f[n]

Constant == [][x' = x]_vars

THEOREM Spec => [](TypeOK /\ InRange)

=============================================================================================
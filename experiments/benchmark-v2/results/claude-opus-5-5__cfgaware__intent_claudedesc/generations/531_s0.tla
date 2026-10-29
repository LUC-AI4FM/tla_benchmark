---------------------------- MODULE IntDivision ----------------------------
EXTENDS Integers

CONSTANTS MSet, NSet

ConstMSet == -6..6
ConstNSet == 1..4

ASSUME MSet \subseteq Int
ASSUME NSet \subseteq Int

VARIABLES m, n, q, r, pc

vars == <<m, n, q, r, pc>>

Abs(x) == IF x < 0 THEN -x ELSE x

Init ==
    /\ m \in MSet
    /\ n \in NSet \ {0}
    /\ q = 0
    /\ r = m
    /\ pc = "loop"

\* Non-negative remainder: subtract divisor while remainder too large
SubStep ==
    /\ pc = "loop"
    /\ r >= Abs(n)
    /\ r' = r - Abs(n)
    /\ q' = IF n > 0 THEN q + 1 ELSE q - 1
    /\ UNCHANGED <<m, n, pc>>

\* Negative remainder: add divisor until remainder is non-negative
AddStep ==
    /\ pc = "loop"
    /\ r < 0
    /\ r' = r + Abs(n)
    /\ q' = IF n > 0 THEN q - 1 ELSE q + 1
    /\ UNCHANGED <<m, n, pc>>

Finish ==
    /\ pc = "loop"
    /\ r >= 0
    /\ r < Abs(n)
    /\ pc' = "done"
    /\ UNCHANGED <<m, n, q, r>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == SubStep \/ AddStep \/ Finish \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(SubStep \/ AddStep \/ Finish)

------------------------------------------------------------------------------
TypeOK ==
    /\ m \in Int
    /\ n \in Int \ {0}
    /\ q \in Int
    /\ r \in Int
    /\ pc \in {"loop", "done"}

LoopInvariant == m = q * n + r

DivisionCorrect ==
    pc = "done" => m = q * n + r

RemainderBounds ==
    pc = "done" => (0 <= r /\ r < Abs(n))

SignCorrect ==
    pc = "done" => ((m < 0 /\ n > 0) => q < 0)

Correctness == DivisionCorrect /\ RemainderBounds /\ SignCorrect

Termination == <>(pc = "done")
==============================================================================
------------------------------ MODULE Fingerprint ------------------------------
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

IntDomain == {0, 1}
RecDomain == {0}

IntRange == SUBSET {2, 3, 4}
RecRange == SUBSET [a : {1, 2}, b : {3}]

Init ==
    /\ x \in [IntDomain -> IntRange]
    /\ y \in [RecDomain -> RecRange]

(* Each transition writes a value that is mathematically equal to a value
   already present in the initial state space, but written differently.
   If fingerprinting normalizes correctly, no new states are discovered. *)

SetDup ==
    /\ x' = [x EXCEPT ![0] = {4, 4, 3}]
    /\ UNCHANGED y

SetDupSingle ==
    /\ x' = [x EXCEPT ![1] = {2, 2}]
    /\ UNCHANGED y

SetOrder ==
    /\ x' = [x EXCEPT ![0] = {4, 3, 2}, ![1] = {3, 2, 4, 2}]
    /\ UNCHANGED y

SetWhole ==
    /\ x' = [i \in {1, 0, 1} |-> IF i = 0 THEN {3, 3, 2} ELSE {}]
    /\ UNCHANGED y

RecFieldOrder ==
    /\ y' = [y EXCEPT ![0] = {[b |-> 3, a |-> 1], [a |-> 1, b |-> 3], [b |-> 3, a |-> 2]}]
    /\ UNCHANGED x

RecFieldDup ==
    /\ y' \in [{0, 0} -> SUBSET [b : {3, 3}, a : {2, 1, 1, 2}]]
    /\ UNCHANGED x

RecMixed ==
    /\ y' = [i \in {0} |-> {[b |-> 3, a |-> 2], [a |-> 2, b |-> 3]}]
    /\ x' = [i \in {1, 0} |-> {4, 2, 4}]

Next ==
    \/ SetDup
    \/ SetDupSingle
    \/ SetOrder
    \/ SetWhole
    \/ RecFieldOrder
    \/ RecFieldDup
    \/ RecMixed

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in [IntDomain -> IntRange]
    /\ y \in [RecDomain -> RecRange]

Inv ==
    /\ Assert({2, 2} = {2}, "Set normalization failed: {2,2} # {2}")
    /\ Assert({4, 4, 3} = {3, 4}, "Set normalization failed: {4,4,3} # {3,4}")
    /\ Assert({4, 3, 2} = {2, 3, 4}, "Set ordering failed: {4,3,2} # {2,3,4}")
    /\ Assert([a |-> 1, b |-> 3] = [b |-> 3, a |-> 1],
              "Record field order failed")
    /\ Assert([a : {1, 1, 2}, b : {3, 3}] = [b : {3}, a : {2, 1}],
              "Record set normalization failed")
    /\ Assert({[b |-> 3, a |-> 1], [a |-> 1, b |-> 3]} = {[a |-> 1, b |-> 3]},
              "Set of equal records not normalized")
    /\ Assert([i \in {1, 0, 1} |-> i] = [i \in {0, 1} |-> i],
              "Function domain normalization failed")
    /\ Assert(TypeOK, "State left the initial state space")
=============================================================================
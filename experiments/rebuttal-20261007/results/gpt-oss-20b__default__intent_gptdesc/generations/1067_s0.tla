MODULE RingTermination
EXTENDS Naturals, TLC

CONSTANT N
ASSUME N > 0

ProcSet == 1..N

VARIABLES active, terminated

vars == <<active, terminated>>

Init ==
    /\ active \in [ProcSet -> BOOLEAN]
    /\ terminated = FALSE

LocalTermination(p) ==
    /\ p \in ProcSet
    /\ active[p] = TRUE
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ terminated' = terminated

Activation(p, q) ==
    /\ p \in ProcSet
    /\ q \in ProcSet
    /\ p # q
    /\ active[p] = TRUE
    /\ active[q] = FALSE
    /\ active' = [active EXCEPT ![q] = TRUE]
    /\ terminated' = terminated

Detection ==
    /\ (\A p \in ProcSet : active[p] = FALSE)
    /\ terminated = FALSE
    /\ terminated' = TRUE
    /\ active' = active

Next == 
    \/ \E p \in ProcSet : LocalTermination(p)
    \/ \E p,q \in ProcSet : Activation(p,q)
    \/ Detection

SafetyInvariant ==
    terminated => (\A p \in ProcSet : active[p] = FALSE)

QuiescencePersistence ==
    [] ((\A p \in ProcSet : active[p] = FALSE) => (\A p \in ProcSet : active'[p] = FALSE))

LivenessProperty ==
    [] ((\A p \in ProcSet : active[p] = FALSE) => <> terminated)

Spec == Init /\ [][Next]_vars /\ LivenessProperty /\ WEAK FAIRNESS Detection /\ QuiescencePersistence /\ SafetyInvariant

===============================================================================
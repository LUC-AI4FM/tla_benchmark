MODULE SimpleBarrier

EXTENDS Naturals, TLC

CONSTANT N
ASSUME N > 0

ProcessSet == 1..N
StateValues == {"b0", "b1"}

VARIABLE pc

TypeCorrectness == pc \in [ProcessSet -> StateValues]

Init == pc = [p \in ProcessSet |-> "b0"]

Individual(p) ==
    /\ p \in ProcessSet
    /\ pc[p] = "b0"
    /\ pc' = [pc EXCEPT ![p] = "b1"]

ResetAll ==
    /\ \A q \in ProcessSet : pc[q] = "b1"
    /\ pc' = [q \in ProcessSet |-> "b0"]

Next == (\E p \in ProcessSet : Individual(p)) \/ ResetAll

BarrierProp ==
    [] ((\E p \in ProcessSet : (pc'[p] = "b0" /\ pc[p] = "b1")) => (\A q \in ProcessSet : pc[q] = "b1"))

Spec == Init /\ [][Next]_<<pc>> /\ TypeCorrectness /\ BarrierProp

(* END OF MODULE *)
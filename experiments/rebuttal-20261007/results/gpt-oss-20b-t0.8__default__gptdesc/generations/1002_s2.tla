MODULE Barrier
EXTENDS Naturals, TLC

CONSTANTS N

PROCESS == 1 .. N

VARIABLE pc

(* Type correctness invariant for the program counter function *)
TypeOK ==
    pc \in [PROCESS -> {"b0", "b1"}]
    /\ DOMAIN(pc) = PROCESS

Init ==
    pc = [p \in PROCESS |-> "b0"]

MoveToB1 ==
    ∃ p \in PROCESS :
        pc[p] = "b0" 
        /\ pc' = [pc EXCEPT ![p] = "b1"]

ResetAll ==
    (∀ p \in PROCESS : pc[p] = "b1")
    /\ pc' = [p \in PROCESS |-> "b0"]

Next == MoveToB1 \/ ResetAll

Spec == Init /\ [][Next]_pc /\ []TypeOK

===============================================================================
------------------------------ MODULE Barrier ------------------------------
EXTENDS Naturals, TLC

CONSTANT N
VARIABLE pc

(* Process set *)
ProcSet == 1..N

(* Type correctness of the program counter function *)
TypeInv ==
    DOMAIN pc = ProcSet /\
    ∀p \in ProcSet : pc[p] \in {"b0", "b1"}

Init ==
    TypeInv /\ 
    ∀p \in ProcSet : pc[p] = "b0"

Next ==
    (∃p \in ProcSet :
        pc[p] = "b0" /\
        pc' = [pc EXCEPT ![p] = "b1"]) \/ 
    (∀p \in ProcSet : pc[p] = "b1" /\ 
        pc' = [p \in ProcSet |-> "b0"])

Spec == Init /\ []Next /\ [](TypeInv)

=============================================================================
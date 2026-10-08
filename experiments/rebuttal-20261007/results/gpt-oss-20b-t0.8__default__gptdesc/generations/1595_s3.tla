MODULE FairCounter

EXTENDS Integers, TLC

CONSTANT MaxCount \* The maximum count value, e.g., 10

VARIABLES x, pc

(* --- Initialization ----------------------------------------------------- *)
Init == /\ x = 0
        /\ pc = "Init"

(* --- Next-state relation ----------------------------------------------- *)
Next ==
    \/ /\ pc = "Init"
       /\ pc' = "Loop"
       /\ x'   = 0
    \/ /\ pc = "Loop" /\ x < MaxCount
       /\ pc' = "Loop"
       /\ x'   = x + 1
    \/ /\ pc = "Loop" /\ x = MaxCount
       /\ pc' = "Done"
       /\ x'   = x
    \/ /\ pc = "Done"
       /\ pc' = "Done"
       /\ x'   = x

(* --- Auxiliary predicates ---------------------------------------------- *)
AtFive == x = 5

FinishLoop == pc = "Done"

PossibleCounts ==
        /\ 0 <= x <= MaxCount
        /\ pc \in {"Init", "Loop", "Done"}

(* --- Specification ----------------------------------------------------- *)
Spec == Init
       /\ [] Next
       /\ WF_M(Next)
       /\ [] PossibleCounts
       /\ <> (pc = "Done")

(* ----------------------------------------------------------------------- *)

CHECKPOINT := [x |-> 0, pc |-> "Init"]

END MODULE
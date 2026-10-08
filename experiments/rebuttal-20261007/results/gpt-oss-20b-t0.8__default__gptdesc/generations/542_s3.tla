----------------------------- MODULE PlusCalIncrement -----------------------------
EXTENDS Integers

CONSTANTS ProcA, ProcB

VARIABLE x, pc

(*---*  State Space *---*)

State == /\ x \in Nat
        /\ pc \in [ {ProcA, ProcB} -> {"Start", "Done"} ]

Init ==
    /\ x = 0
    /\ pc[ProcA] = "Start"
    /\ pc[ProcB] = "Start"

(*---*  Actions *---*)

Increment(p) == 
    /\ p \in {ProcA, ProcB}
    /\ pc[p] = "Start"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]

Terminating ==
    /\ pc[ProcA] = "Done" 
    /\ pc[ProcB] = "Done"
    /\ UNCHANGED <<x, pc>>

Next == Increment(ProcA) \/ Increment(ProcB) \/ Terminating

(*---*  Invariants *---*)

(* No additional safety invariants required *)

(*---*  Temporal Properties *---*)

TerminationProp ==
    [] (pc[ProcA] = "Done" /\ pc[ProcB] = "Done") => 
        <> (pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

Spec == Init /\ [][Next]_<<x, pc>> 

=============================================================================
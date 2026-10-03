---------------------------- MODULE PlusCalSpec ----------------------------
EXTENDS Integers

CONSTANT ProcA, ProcB
VARIABLE x, pc

Init == (pc = [ProcA |-> "Start", ProcB |-> "Start"] /\ x = 0)

TypeOK == (* Type invariant *)
         pc[ProcA] \in {"Start", "Done"} /\ 
         pc[ProcB] \in {"Start", "Done"}

NextA == (* ProcA action *)
        pc[ProcA] = "Start" /\
        x' = x + 1 /\
        pc' = [pc EXCEPT ![ProcA] = "Done"] /\ 
        UNCHANGED <<pc[ProcB], x>>

NextB == (* ProcB action *)
        pc[ProcB] = "Start" /\
        x' = x + 1 /\
        pc' = [pc EXCEPT ![ProcB] = "Done"] /\ 
        UNCHANGED <<pc[ProcA], x>>

Terminating == (* Terminating action to allow stuttering *)
               (pc[ProcA] = "Done") /\ (pc[ProcB] = "Done")

Next == NextA \/ NextB \/ Terminating

Spec == Init /\ [][Next]_<<x, pc>> /\ <>[](pc[ProcA] = "Done" /\ pc[ProcB] = "Done")
=============================================================================
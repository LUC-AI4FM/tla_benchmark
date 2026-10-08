---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences

CONSTANT ProcSet

VARIABLES x, pc

vars == << x, pc >>

ProcA == "ProcA"
ProcB == "ProcB"

Init == 
    /\ x = 0
    /\ pc = [self \in {ProcA, ProcB} |-> 
                CASE self = ProcA -> "a"
                  [] self = ProcB -> "b"]

a == 
    /\ pc[ProcA] = "a"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcA] = "Done"]

b == 
    /\ pc[ProcB] = "b"
    /\ x' = x + 1
    /\ pc' = [pc EXCEPT ![ProcB] = "Done"]

Terminating == 
    /\ pc[ProcA] = "Done"
    /\ pc[ProcB] = "Done"
    /\ UNCHANGED vars

Next == 
    \/ a
    \/ b
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc[ProcA] = "Done" /\ pc[ProcB] = "Done")

=============================================================================
---------------------------- MODULE SimpleCounter ----------------------------
EXTENDS Integers, TLC

CONSTANTS ProcA, ProcB

VARIABLES x, pc

vars == << x, pc >>

ProcSet == {ProcA} \cup {ProcB}

Init == 
    /\ x = 0
    /\ pc = [self \in ProcSet |-> CASE self = ProcA -> "a"
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
    /\ \A self \in ProcSet: pc[self] = "Done"
    /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

TypeOK ==
    /\ x \in Int
    /\ pc \in [ProcSet -> {"a", "b", "Done"}]

FinalValue == (\A self \in ProcSet: pc[self] = "Done") => x = 2

=============================================================================
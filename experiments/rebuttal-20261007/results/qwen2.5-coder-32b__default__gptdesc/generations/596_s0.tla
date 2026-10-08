------------------------------- MODULE OneVarSystem -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS x

VARIABLES val

Init == val = 0

Next ==
    \/ /\ val = 0
       /\ \E v \in {1, 2} : val' = v
    \/ /\ val # 0
       /\ val' = 0

Spec ==
    /\ Init
    /\ [][Next]_<<val>>
    /\ WF_x(Next)

StabilizeAwayFromOneOrTwo == <>[] (val # 1) /\ (val # 2)
RepeatedReturnToZero == <>(\A n \in Nat : val = 0)

NegatedProperty == ~<>(\A n \in Nat : val = 1)

Postcondition ==
    LET trace == <<[val |-> 0], [val |-> 1], [val |-> 0], [val |-> 2], [val |-> 0]>>
    IN  /\ Len(trace) > 0
        /\ \A i \in 1..Len(trace)-1 : trace[i] \in {[val |-> 0], [val |-> 1], [val |-> 2]}
        /\ \A i \in 1..Len(trace)-1 : trace[i+1] = [trace[i] EXCEPT ![val] = IF trace[i][val] = 0 THEN CHOOSE v \in {1, 2} ELSE 0]

=============================================================================
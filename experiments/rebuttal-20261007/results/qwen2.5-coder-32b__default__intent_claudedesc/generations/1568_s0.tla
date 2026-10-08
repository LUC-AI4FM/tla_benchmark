------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcesses, MaxTicket

VARIABLES choosing, number

Init == /\ choosing \in [1..NumProcesses -> BOOLEAN]
        /\ number \in [1..NumProcesses -> 0..MaxTicket]
        /\ (\A p \in 1..NumProcesses : choosing[p] = FALSE)
        /\ (\A p \in 1..NumProcesses : number[p] = 0)

ChooseNumber ==
    \E p \in 1..NumProcesses :
        /\ choosing' = [choosing EXCEPT ![p] = TRUE]
        /\ number' = [number EXCEPT ![p] = (MAX({number[q] : q \in 1..NumProcesses}) + 1)]
        /\ UNCHANGED {choosing[q], number[q] : q \in 1..NumProcesses \ {p}}

WaitForChoosing ==
    \E p \in 1..NumProcesses :
        /\ choosing' = [choosing EXCEPT ![p] = FALSE]
        /\ UNCHANGED {number[q] : q \in 1..NumProcesses}
        /\ (\A q \in 1..NumProcesses \ {p} : choosing[q] => number'[q] = number[q])

WaitForPriority ==
    \E p \in 1..NumProcesses :
        /\ UNCHANGED choosing
        /\ UNCHANGED {number[q] : q \in 1..NumProcesses}
        /\ (\A q \in 1..NumProcesses \ {p} :
            \/ number[p] < number[q]
            \/ (number[p] = number[q] /\ p < q))

Next ==
    ChooseNumber \/ WaitForChoosing \/ WaitForPriority

Spec == Init /\ [][Next]_<<choosing, number>>

MutualExclusion ==
    \A p, q \in 1..NumProcesses :
        p # q => ~(\E s \in StateTrace : (number[s][p] > 0) /\ (number[s][q] > 0))

THEOREM Spec => [] MutualExclusion
=============================================================================
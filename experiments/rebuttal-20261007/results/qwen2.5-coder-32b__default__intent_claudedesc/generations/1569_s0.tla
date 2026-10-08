------------------------------- MODULE BakeryMutex -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcesses, MaxTicket

VARIABLES tickets, choosing

Init == /\ tickets \in [1..NumProcesses -> {0}]
        /\ choosing \in [1..NumProcesses -> BOOLEAN]
        /\ (\A p \in 1..NumProcesses : tickets[p] = 0)
        /\ (\A p \in 1..NumProcesses : \neg choosing[p])

ChooseTicket ==
    \E p \in 1..NumProcesses :
        \E order \in Permutations({1..NumProcesses} \ {p}) :
            /\ choosing' = [choosing EXCEPT ![p] = TRUE]
            /\ tickets' = [tickets EXCEPT ![p] = (Max( {tickets[q] : q \in 1..NumProcesses, q # p} ) + 1)]
            /\ \/ \A q \in order : \neg choosing[q]
               \/ \E r \in order : choosing[r]

Wait ==
    \E p \in 1..NumProcesses :
        \E order \in Permutations({1..NumProcesses} \ {p}) :
            /\ \A q \in order :
                \/ tickets[q] = 0
                \/ tickets[p] < tickets[q]
                \/ (tickets[p] = tickets[q] /\ p < q)
            /\ choosing' = [choosing EXCEPT ![p] = FALSE]

Next == ChooseTicket \/ Wait

Spec ==
    /\ Init
    /\ [][Next]_<<tickets, choosing>>
    /\ WF_next(<<tickets, choosing>>)

MutualExclusion ==
    \A p, q \in 1..NumProcesses :
        p # q => ~(\E s \in StateTrace : tickets[s][p] > 0 /\ tickets[s][q] > 0)

StateConstraint ==
    \A p \in 1..NumProcesses : tickets[p] \leq MaxTicket

=============================================================================
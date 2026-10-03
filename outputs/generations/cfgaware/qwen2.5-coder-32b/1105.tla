------------------------------- MODULE AsyncCommit -------------------------------

CONSTANTS N \* Number of processes

VARIABLES votes, messages, suspected, state

\* Possible states for each process
CONSTANT <<ABORT>>, <<COMMIT>>, <<WAITING>>

\* Type invariant: 
TypeOK == /\ votes \in [1..N -> {"YES", "NO"}]
          /\ messages \in [1..N -> [1..N -> BOOLEAN]]
          /\ suspected \in [1..N -> BOOLEAN]
          /\ state \in [1..N -> {<<ABORT>>, <<COMMIT>>, <<WAITING>>}]

\* Initial predicate: All processes vote either all "YES" or all "NO"
Init == \/ (\A p \in 1..N : votes[p] = "YES")
        \/ (\A p \in 1..N : votes[p] = "NO")

\* Next state relation
Next ==
    \E p \in 1..N :
        LET msgToSend == [q \in 1..N | q # p -> messages[p][q]]
            allSuspected == \A q \in 1..N : suspected[q]
            receivedMsgs == [q \in 1..N | q # p -> messages[q][p]]
            voteCount[v] == \# {q \in 1..N : votes[q] = v}
        IN
        \/ /\ state[p] = <<WAITING>>
           /\ ~suspected[p]
           /\ (voteCount["YES"] > N \div 2) 
              -> ['][state EXCEPT ![p] = <<COMMIT>>]
           \/ (voteCount["NO"] > N \div 2)
              -> ['][state EXCEPT ![p] = <<ABORT>>]
        \/ /\ state[p] = <<WAITING>>
           /\ suspected[p]
           -> ['][state EXCEPT ![p] = <<ABORT>>]

\* Weak fairness for non-stuttering process actions
WF == WF_next(Init, Next)

\* Specification
Spec ==
    Init /\ [][Next]_<<votes, messages, suspected, state>> /\ SF WF

\* Temporal properties
AgrrLtl == [](state[p] = <<COMMIT>> => \A q \in 1..N : votes[q] = "YES") 
           \/ [](state[p] = <<ABORT>> => \A q \in 1..N : votes[q] = "NO")

AbortValidityLtl ==
    [](state[p] = <<ABORT>> => (\E q \in 1..N : suspected[q]) \/ (voteCount["NO"] > N \div 2))

CommitValidityLtl ==
    [](state[p] = <<COMMIT>> => voteCount["YES"] > N \div 2)

TerminationLtl == <>(\A p \in 1..N : state[p] \in {<<ABORT>>, <<COMMIT>>})

=============================================================================
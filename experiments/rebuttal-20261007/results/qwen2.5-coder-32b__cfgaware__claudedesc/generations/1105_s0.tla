------------------------------- MODULE NBAC -----------------------------------

CONSTANTS N \* Number of processes

VARIABLES nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail

\* Process states
CONSTANT <<YES, NO, SENT, ABORT, COMMIT, BYZ>>

\* Initial predicate for SpecYes
InitYes == /\ nSntYes = [p \in 1..N -> 0]
           /\ nSntNo = [p \in 1..N -> 0]
           /\ nSntYesF = [p \in 1..N -> 0]
           /\ nSntNoF = [p \in 1..N -> 0]
           /\ nRcvdYes = [p \in 1..N -> [q \in 1..N -> 0]]
           /\ nRcvdNo = [p \in 1..N -> [q \in 1..N -> 0]]
           /\ pc = [p \in 1..N -> YES]
           /\ someFail = [p \in 1..N -> FALSE]

\* Initial predicate for SpecNo
InitNo == /\ nSntYes = [p \in 1..N -> 0]
          /\ nSntNo = [p \in 1..N -> 0]
          /\ nSntYesF = [p \in 1..N -> 0]
          /\ nSntNoF = [p \in 1..N -> 0]
          /\ nRcvdYes = [p \in 1..N -> [q \in 1..N -> 0]]
          /\ nRcvdNo = [p \in 1..N -> [q \in 1..N -> 0]]
          /\ pc = [p \in 1..N -> NO]
          /\ someFail = [p \in 1..N -> FALSE]

\* Action: SendYes
SendYes ==
    \E p \in 1..N :
        /\ pc[p] = YES
        /\ someFail[p] = FALSE
        /\ \/ nSntYes' = [nSntYes EXCEPT ![p] = nSntYes[p] + 1]
           /\ nSntNo' = nSntNo
           /\ nSntYesF' = nSntYesF
           /\ nSntNoF' = nSntNoF
           /\ nRcvdYes' = [nRcvdYes EXCEPT ![p] = [q \in 1..N -> IF q # p THEN nRcvdYes[p][q] + 1 ELSE nRcvdYes[p][q]]]
           /\ nRcvdNo' = nRcvdNo
           /\ pc' = [pc EXCEPT ![p] = SENT]
           /\ someFail' = someFail

\* Action: SendNo
SendNo ==
    \E p \in 1..N :
        /\ pc[p] = NO
        /\ someFail[p] = FALSE
        /\ \/ nSntYes' = nSntYes
           /\ nSntNo' = [nSntNo EXCEPT ![p] = nSntNo[p] + 1]
           /\ nSntYesF' = nSntYesF
           /\ nSntNoF' = nSntNoF
           /\ nRcvdYes' = nRcvdYes
           /\ nRcvdNo' = [nRcvdNo EXCEPT ![p] = [q \in 1..N -> IF q # p THEN nRcvdNo[p][q] + 1 ELSE nRcvdNo[p][q]]]
           /\ pc' = [pc EXCEPT ![p] = SENT]
           /\ someFail' = someFail

\* Action: Receive
Receive ==
    \E p \in 1..N :
        /\ pc[p] = SENT
        /\ someFail[p] = FALSE
        /\ \/ nSntYes' = nSntYes
           /\ nSntNo' = nSntNo
           /\ nSntYesF' = nSntYesF
           /\ nSntNoF' = nSntNoF
           /\ nRcvdYes' = [nRcvdYes EXCEPT ![p] = [q \in 1..N -> IF q # p THEN nRcvdYes[p][q] + 1 ELSE nRcvdYes[p][q]]]
           /\ nRcvdNo' = [nRcvdNo EXCEPT ![p] = [q \in 1..N -> IF q # p THEN nRcvdNo[p][q] + 1 ELSE nRcvdNo[p][q]]]
           /\ pc' = pc
           /\ someFail' = someFail

\* Action: Commit
Commit ==
    \E p \in 1..N :
        /\ pc[p] = SENT
        /\ someFail[p] = FALSE
        /\ LET totalYes == SUM {nRcvdYes[p][q] : q \in 1..N}
           totalNo == SUM {nRcvdNo[p][q] : q \in 1..N} IN
        /\ totalYes >= N - 1
        /\ totalNo = 0
        /\ \/ nSntYes' = nSntYes
           /\ nSntNo' = nSntNo
           /\ nSntYesF' = nSntYesF
           /\ nSntNoF' = nSntNoF
           /\ nRcvdYes' = nRcvdYes
           /\ nRcvdNo' = nRcvdNo
           /\ pc' = [pc EXCEPT ![p] = COMMIT]
           /\ someFail' = someFail

\* Action: AbortSent
AbortSent ==
    \E p \in 1..N :
        /\ pc[p] = SENT
        /\ someFail[p] = FALSE
        /\ LET totalNo == SUM {nRcvdNo[p][q] : q \in 1..N} IN
        /\ totalNo > 0
        /\ \/ nSntYes' = nSntYes
           /\ nSntNo' = nSntNo
           /\ nSntYesF' = nSntYesF
           /\ nSntNoF' = nSntNoF
           /\ nRcvdYes' = nRcvdYes
           /\ nRcvdNo' = nRcvdNo
           /\ pc' = [pc EXCEPT ![p] = ABORT]
           /\ someFail' = someFail

\* Action: AbortNoYes
AbortNoYes ==
    \E p \in 1..N :
        /\ pc[p] = NO
        /\ someFail[p] = FALSE
        /\ \/ nSntYes' = nSntYes
           /\ nSntNo' = nSntNo
           /\ nSntYesF' = nSntYesF
           /\ nSntNoF' = nSntNoF
           /\ nRcvdYes' = nRcvdYes
           /\ nRcvdNo' = nRcvdNo
           /\ pc' = [pc EXCEPT ![p] = ABORT]
           /\ someFail' = someFail

\* Action: Crash
Crash ==
    \E p \in 1..N :
        /\ pc[p] \notin {COMMIT, ABORT}
        /\ someFail[p] = FALSE
        /\ \/ nSntYes' = [nSntYes EXCEPT ![p] = nSntYes[p] + 1]
           /\ nSntNo' = [nSntNo EXCEPT ![p] = nSntNo[p] + 1]
           /\ nSntYesF' = [nSntYesF EXCEPT ![p] = nSntYesF[p] + N - 1]
           /\ nSntNoF' = [nSntNoF EXCEPT ![p] = nSntNoF[p] + N - 1]
           /\ nRcvdYes' = nRcvdYes
           /\ nRcvdNo' = nRcvdNo
           /\ pc' = [pc EXCEPT ![p] = BYZ]
           /\ someFail' = [someFail EXCEPT ![p] = TRUE]

\* Next-state relation
Next ==
    \/ SendYes
    \/ SendNo
    \/ Receive
    \/ Commit
    \/ AbortSent
    \/ AbortNoYes
    \/ Crash

\* Specification with initial condition for SpecYes
SpecYes == InitYes /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>

\* Specification with initial condition for SpecNo
SpecNo == InitNo /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>

\* Combined specification
Spec == \/ SpecYes
        \/ SpecNo

\* TypeOK invariant
TypeOK ==
    /\ \A p \in 1..N : pc[p] \in {YES, NO, SENT, ABORT, COMMIT, BYZ}
    /\ \A p \in 1..N : someFail[p] \in BOOLEAN
    /\ \A p \in 1..N : nSntYes[p] >= 0
    /\ \A p \in 1..N : nSntNo[p] >= 0
    /\ \A p \in 1..N : nSntYesF[p] >= 0
    /\ \A p \in 1..N : nSntNoF[p] >= 0
    /\ \A p \in 1..N, q \in 1..N : nRcvdYes[p][q] >= 0
    /\ \A p \in 1..N, q \in 1..N : nRcvdNo[p][q] >= 0

\* Agreement property (LTL)
AgrrLtl ==
    [](\/ pc[1] = ABORT \/ pc[1] = COMMIT) -> [](\A p \in 2..N: pc[p] = pc[1])

\* Abort validity property (LTL)
AbortValidityLtl ==
    [](\/ \E p \in 1..N : pc[p] = NO) -> [](\/ \A p \in 1..N : pc[p] = ABORT)

\* Commit validity property (LTL)
CommitValidityLtl ==
    [](\/ \A p \in 1..N : pc[p] = YES /\ someFail[p] = FALSE) -> [](\/ \A p \in 1..N : pc[p] = COMMIT)

\* Termination property (LTL)
TerminationLtl ==
    [](\/ \A p \in 1..N : pc[p] \notin {YES, NO}) -> <>(\/ \A p \in 1..N : pc[p] \in {COMMIT, ABORT})

=============================================================================
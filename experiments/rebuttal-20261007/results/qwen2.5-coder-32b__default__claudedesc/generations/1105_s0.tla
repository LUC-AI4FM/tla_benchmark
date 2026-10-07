------------------------------- MODULE NBAC -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N = 3

VARIABLES nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail

Init == 
    /\ nSntYes = 0
    /\ nSntNo = 0
    /\ nSntYesF = 0
    /\ nSntNoF = 0
    /\ nRcvdYes \in [1..N -> 0]
    /\ nRcvdNo \in [1..N -> 0]
    /\ pc \in [1..N -> {"YES", "NO"}]
    /\ someFail \in [1..N -> FALSE]

SendYes(p) ==
    /\ pc[p] = "YES"
    /\ someFail[p] = FALSE
    /\ nSntYes' = nSntYes + 1
    /\ nSntNo' = nSntNo
    /\ nSntYesF' = nSntYesF
    /\ nSntNoF' = nSntNoF
    /\ nRcvdYes' = nRcvdYes
    /\ nRcvdNo' = nRcvdNo
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ someFail' = someFail

SendNo(p) ==
    /\ pc[p] = "NO"
    /\ someFail[p] = FALSE
    /\ nSntYes' = nSntYes
    /\ nSntNo' = nSntNo + 1
    /\ nSntYesF' = nSntYesF
    /\ nSntNoF' = nSntNoF
    /\ nRcvdYes' = nRcvdYes
    /\ nRcvdNo' = nRcvdNo
    /\ pc' = [pc EXCEPT ![p] = "SENT"]
    /\ someFail' = someFail

Receive(p, q) ==
    /\ pc[p] = "SENT"
    /\ someFail[q] = FALSE
    /\ \/ (pc[q] = "YES" /\ nRcvdYes'[p] = nRcvdYes[p] + 1)
       \/ (pc[q] = "NO" /\ nRcvdNo'[p] = nRcvdNo[p] + 1)
    /\ nSntYes' = nSntYes
    /\ nSntNo' = nSntNo
    /\ nSntYesF' = nSntYesF
    /\ nSntNoF' = nSntNoF
    /\ nRcvdYes' = [nRcvdYes EXCEPT ![p] = nRcvdYes'[p]]
    /\ nRcvdNo' = [nRcvdNo EXCEPT ![p] = nRcvdNo'[p]]
    /\ pc' = pc
    /\ someFail' = someFail

Commit(p) ==
    /\ pc[p] = "SENT"
    /\ nRcvdYes[p] >= N - 1
    /\ nRcvdNo[p] = 0
    /\ nSntYes' = nSntYes
    /\ nSntNo' = nSntNo
    /\ nSntYesF' = nSntYesF
    /\ nSntNoF' = nSntNoF
    /\ nRcvdYes' = nRcvdYes
    /\ nRcvdNo' = nRcvdNo
    /\ pc' = [pc EXCEPT ![p] = "COMMIT"]
    /\ someFail' = someFail

AbortSent(p) ==
    /\ pc[p] = "SENT"
    /\ nRcvdNo[p] > 0
    /\ nSntYes' = nSntYes
    /\ nSntNo' = nSntNo
    /\ nSntYesF' = nSntYesF
    /\ nSntNoF' = nSntNoF
    /\ nRcvdYes' = nRcvdYes
    /\ nRcvdNo' = nRcvdNo
    /\ pc' = [pc EXCEPT ![p] = "ABORT"]
    /\ someFail' = someFail

AbortNoYes(p) ==
    /\ pc[p] = "NO"
    /\ someFail[p] = TRUE
    /\ nSntYes' = nSntYes
    /\ nSntNo' = nSntNo
    /\ nSntYesF' = nSntYesF + 1
    /\ nSntNoF' = nSntNoF
    /\ nRcvdYes' = nRcvdYes
    /\ nRcvdNo' = nRcvdNo
    /\ pc' = [pc EXCEPT ![p] = "ABORT"]
    /\ someFail' = someFail

Crash(p) ==
    /\ pc[p] \in {"YES", "NO"}
    /\ someFail[p] = FALSE
    /\ nSntYes' = nSntYes
    /\ nSntNo' = nSntNo
    /\ nSntYesF' = nSntYesF + (IF pc[p] = "YES" THEN 1 ELSE 0)
    /\ nSntNoF' = nSntNoF + (IF pc[p] = "NO" THEN 1 ELSE 0)
    /\ nRcvdYes' = nRcvdYes
    /\ nRcvdNo' = nRcvdNo
    /\ pc' = [pc EXCEPT ![p] = "BYZ"]
    /\ someFail' = [someFail EXCEPT ![p] = TRUE]

Next ==
    \/ \E p \in 1..N : SendYes(p)
    \/ \E p \in 1..N : SendNo(p)
    \/ \E p, q \in 1..N : Receive(p, q) /\ p # q
    \/ \E p \in 1..N : Commit(p)
    \/ \E p \in 1..N : AbortSent(p)
    \/ \E p \in 1..N : AbortNoYes(p)
    \/ \E p \in 1..N : Crash(p)

Spec ==
    /\ Init
    /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>
    /\ WF_next(<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>)

SpecYes ==
    /\ Init
    /\ \A p \in 1..N : pc[p] = "YES"
    /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>
    /\ WF_next(<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>)

SpecNo ==
    /\ Init
    /\ \A p \in 1..N : pc[p] = "NO"
    /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>
    /\ WF_next(<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>)

TypeOK ==
    /\ nSntYes \in Nat
    /\ nSntNo \in Nat
    /\ nSntYesF \in Nat
    /\ nSntNoF \in Nat
    /\ nRcvdYes \in [1..N -> Nat]
    /\ nRcvdNo \in [1..N -> Nat]
    /\ pc \in [1..N -> {"YES", "NO", "SENT", "ABORT", "COMMIT", "BYZ"}]
    /\ someFail \in [1..N -> BOOLEAN]

Agreement ==
    \/ \A p, q \in 1..N : (pc[p] = "COMMIT" => pc[q] = "COMMIT")
    \/ \A p, q \in 1..N : (pc[p] = "ABORT" => pc[q] = "ABORT")

AbortValidity ==
    /\ \E p \in 1..N : pc[p] = "NO"
    => \A q \in 1..N : pc[q] # "COMMIT"

CommitValidity ==
    /\ nSntNoF = 0
    /\ nSntYes >= N - 1
    => \A p \in 1..N : pc[p] = "COMMIT"

Termination ==
    \/ \E p \in 1..N : pc[p] = "COMMIT"
    \/ \E p \in 1..N : pc[p] = "ABORT"

WF_next(vars) == 
    WF_vars(Next, vars)

=============================================================================
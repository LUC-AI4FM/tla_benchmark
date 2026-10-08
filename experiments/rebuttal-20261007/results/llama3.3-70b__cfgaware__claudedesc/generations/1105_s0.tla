---------------------------- MODULE NBAC ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE nSntYes, nSntNo, nSntYesF, nSntNoF, 
         nRcvdYes, nRcvdNo, pc, someFail

TypeOK == 
  /\ nSntYes \in 0..N
  /\ nSntNo \in 0..N
  /\ nSntYesF \in 0..N
  /\ nSntNoF \in 0..N
  /\ nRcvdYes \in [1..N -> 0..N]
  /\ nRcvdNo \in [1..N -> 0..N]
  /\ pc \in [1..N -> {YES, NO, SENT, ABORT, COMMIT, BYZ}]
  /\ someFail \in [1..N -> BOOLEAN]

SendYes(p) == 
  /\ pc[p] = YES
  /\ pc' = [pc EXCEPT ![p] = SENT]
  /\ nSntYes' = nSntYes + 1
  /\ nRcvdYes' = [nRcvdYes EXCEPT ![q \in 1..N |-> IF q = p THEN 0 ELSE nRcvdYes[q]]]
  /\ UNCHANGED <<nSntNo, nSntYesF, nSntNoF, nRcvdNo, someFail>>

SendNo(p) == 
  /\ pc[p] = NO
  /\ pc' = [pc EXCEPT ![p] = SENT]
  /\ nSntNo' = nSntNo + 1
  /\ nRcvdNo' = [nRcvdNo EXCEPT ![q \in 1..N |-> IF q = p THEN 0 ELSE nRcvdNo[q]]]
  /\ UNCHANGED <<nSntYes, nSntYesF, nSntNoF, nRcvdYes, someFail>>

Receive(p) == 
  /\ pc[p] = SENT
  /\ \E q \in 1..N : 
    (pc[q] = YES /\ nRcvdYes'[p] = nRcvdYes[p] + 1)
    \/ (pc[q] = NO /\ nRcvdNo'[p] = nRcvdNo[p] + 1)
  /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, pc, someFail>>

Commit(p) == 
  /\ pc[p] = SENT
  /\ nRcvdYes[p] = N
  /\ nRcvdNo[p] = 0
  /\ pc' = [pc EXCEPT ![p] = COMMIT]
  /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

AbortSent(p) == 
  /\ pc[p] = SENT
  /\ nRcvdNo[p] > 0
  /\ pc' = [pc EXCEPT ![p] = ABORT]
  /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

AbortNoYes(p) == 
  /\ pc[p] \in {YES, NO}
  /\ someFail[p]
  /\ pc' = [pc EXCEPT ![p] = ABORT]
  /\ UNCHANGED <<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail>>

Crash(p) == 
  /\ pc[p] \in {YES, NO, SENT}
  /\ pc' = [pc EXCEPT ![p] = BYZ]
  /\ nSntYesF' = nSntYesF + IF pc[p] = YES THEN 1 ELSE 0
  /\ nSntNoF' = nSntNoF + IF pc[p] = NO THEN 1 ELSE 0
  /\ someFail' = [someFail EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<nSntYes, nSntNo, nRcvdYes, nRcvdNo>>

Next == 
  \E p \in 1..N : 
    SendYes(p) 
    \/ SendNo(p)
    \/ Receive(p)
    \/ Commit(p)
    \/ AbortSent(p)
    \/ AbortNoYes(p)
    \/ Crash(p)

Spec == 
  /\ (nSntYes = 0 /\ nSntNo = 0 /\ nSntYesF = 0 /\ nSntNoF = 0)
  /\ (nRcvdYes = [q \in 1..N |-> 0] /\ nRcvdNo = [q \in 1..N |-> 0])
  /\ (pc = [p \in 1..N |-> YES] /\ someFail = [p \in 1..N |-> FALSE])
  /\ [][Next]_<<nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail>>
  /\ WF_vars(<<SendYes, SendNo, Receive, Commit, AbortSent, AbortNoYes, Crash>>)

AgrrLtl == <>[]\A p,q \in 1..N : (pc[p] = COMMIT) => (pc[q] /= ABORT)
AbortValidityLtl == [](\A p \in 1..N : (nSntNo > 0) => (pc[p] /= COMMIT))
CommitValidityLtl == <>[]\A p \in 1..N : ((nRcvdYes = N) /\ (nRcvdNo = 0)) => (pc[p] = COMMIT)
TerminationLtl == []<>(\A p \in 1..N : (someFail[p] => pc[p] /= BYZ) /\ (pc[p] \in {COMMIT, ABORT}))

THEOREM Spec => AgrrLtl
THEOREM Spec => AbortValidityLtl
THEOREM Spec => CommitValidityLtl
THEOREM Spec => TerminationLtl

====================================================================
------------------------------ MODULE nbacg_guer01 ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail

vars == << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, pc, someFail >>

Proc == 1 .. N

Status == { "YES", "NO", "SENT", "ABORT", "COMMIT", "BYZ" }

-----------------------------------------------------------------------------

InitCommon ==
  /\ nSntYes = 0
  /\ nSntNo = 0
  /\ nSntYesF = 0
  /\ nSntNoF = 0
  /\ nRcvdYes = [ i \in Proc |-> 0 ]
  /\ nRcvdNo = [ i \in Proc |-> 0 ]
  /\ someFail = [ i \in Proc |-> FALSE ]

Init ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ InitCommon

InitYes ==
  /\ pc = [ i \in Proc |-> "YES" ]
  /\ InitCommon

InitNo ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ \E i \in Proc : pc[i] = "NO"
  /\ InitCommon

-----------------------------------------------------------------------------

SendYes(i) ==
  /\ pc[i] = "YES"
  /\ ~someFail[i]
  /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
  /\ nSntYes' = nSntYes + 1
  /\ UNCHANGED << nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

SendNo(i) ==
  /\ pc[i] = "NO"
  /\ ~someFail[i]
  /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
  /\ nSntNo' = nSntNo + 1
  /\ UNCHANGED << nSntYes, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

ReceiveYes(i) ==
  /\ pc[i] = "SENT"
  /\ nRcvdYes[i] < nSntYes + nSntYesF
  /\ nRcvdYes' = [ nRcvdYes EXCEPT ![i] = nRcvdYes[i] + 1 ]
  /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdNo, pc, someFail >>

ReceiveNo(i) ==
  /\ pc[i] = "SENT"
  /\ nRcvdNo[i] < nSntNo + nSntNoF
  /\ nRcvdNo' = [ nRcvdNo EXCEPT ![i] = nRcvdNo[i] + 1 ]
  /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, pc, someFail >>

Receive(i) == ReceiveYes(i) \/ ReceiveNo(i)

Commit(i) ==
  /\ pc[i] = "SENT"
  /\ nRcvdYes[i] = N
  /\ nRcvdNo[i] = 0
  /\ ~someFail[i]
  /\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
  /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

AbortSent(i) ==
  /\ pc[i] = "SENT"
  /\ (nRcvdNo[i] > 0 \/ (someFail[i] /\ nRcvdYes[i] < N))
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

AbortNoYes(i) ==
  /\ pc[i] \in { "YES", "NO" }
  /\ someFail[i]
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

Crash(i) ==
  /\ pc[i] \in { "YES", "NO", "SENT" }
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ nSntYesF' = IF pc[i] = "YES" THEN nSntYesF + 1 ELSE nSntYesF
  /\ nSntNoF' = IF pc[i] = "NO" THEN nSntNoF + 1 ELSE nSntNoF
  /\ someFail' = [ j \in Proc |-> TRUE ]
  /\ UNCHANGED << nSntYes, nSntNo, nRcvdYes, nRcvdNo >>

NonCrashNext ==
  \E i \in Proc :
    \/ SendYes(i)
    \/ SendNo(i)
    \/ Receive(i)
    \/ Commit(i)
    \/ AbortSent(i)
    \/ AbortNoYes(i)

Next ==
  \/ NonCrashNext
  \/ \E i \in Proc : Crash(i)

Fairness == WF_vars(NonCrashNext)

Spec == Init /\ [][Next]_vars /\ Fairness

SpecYes == InitYes /\ [][Next]_vars /\ Fairness

SpecNo == InitNo /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

TypeOK ==
  /\ pc \in [ Proc -> Status ]
  /\ nSntYes \in 0 .. N
  /\ nSntNo \in 0 .. N
  /\ nSntYesF \in 0 .. N
  /\ nSntNoF \in 0 .. N
  /\ nRcvdYes \in [ Proc -> 0 .. N ]
  /\ nRcvdNo \in [ Proc -> 0 .. N ]
  /\ someFail \in [ Proc -> BOOLEAN ]

AgrrLtl ==
  [](\A i, j \in Proc : ~(pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

AbortValidityLtl ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

CommitValidityLtl ==
  ((\A i \in Proc : pc[i] = "YES") /\ [](\A i \in Proc : ~someFail[i]))
    => [](\A i \in Proc : pc[i] # "ABORT")

TerminationLtl ==
  ([](\A i \in Proc : pc[i] # "BYZ" /\ ~someFail[i]))
    => <>(\A i \in Proc : pc[i] \in { "COMMIT", "ABORT" })

=============================================================================
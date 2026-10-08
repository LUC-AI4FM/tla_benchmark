---- MODULE NBAC_CounterAbs ----
EXTENDS Naturals, FiniteSets

(*
  Counter-abstraction NBAC with a perfect failure detector.
  Required bindings: N, TypeOK, AgrrLtl, AbortValidityLtl, CommitValidityLtl, TerminationLtl, Spec
*)

CONSTANTS
(* status atoms as strings to avoid parameterization *)
(* no external constants required *)

N == 3

Proc == 1..N

YES == "YES"
NO == "NO"
SENT == "SENT"
ABORT == "ABORT"
COMMIT == "COMMIT"
BYZ == "BYZ"

Status == {YES, NO, SENT, ABORT, COMMIT, BYZ}

VARIABLES
  pc,           \* [Proc -> Status]
  someFail,     \* [Proc -> BOOLEAN], perfect FD: only crashed processes may be suspected
  nSntYes,      \* Nat, number of YES broadcasts by processes that (at the time of sending) were correct
  nSntNo,       \* Nat, number of NO broadcasts by processes that (at the time of sending) were correct
  nSntYesF,     \* Nat, upper bound on YES votes sent by faulty (crashed-before-send) processes
  nSntNoF,      \* Nat, upper bound on NO votes sent by faulty (crashed-before-send) processes
  nRcvdYes,     \* [Proc -> Nat], per-process received YES count
  nRcvdNo       \* [Proc -> Nat], per-process received NO count

Vars == << pc, someFail, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo >>

Decided(i) == pc[i] \in {COMMIT, ABORT}

TypeOK ==
  /\ pc \in [Proc -> Status]
  /\ someFail \in [Proc -> BOOLEAN]
  /\ nSntYes \in Nat
  /\ nSntNo \in Nat
  /\ nSntYesF \in Nat
  /\ nSntNoF \in Nat
  /\ nRcvdYes \in [Proc -> Nat]
  /\ nRcvdNo \in [Proc -> Nat]
  /\ \A i \in Proc:
       /\ nRcvdYes[i] <= nSntYes + nSntYesF
       /\ nRcvdNo[i]  <= nSntNo  + nSntNoF
       /\ nRcvdYes[i] <= N
       /\ nRcvdNo[i]  <= N
  /\ nSntYes + nSntNo + nSntYesF + nSntNoF <= N
  /\ \A i \in Proc: someFail[i] => pc[i] = BYZ

InitAny ==
  /\ pc \in [Proc -> {YES, NO}]
  /\ someFail = [i \in Proc |-> FALSE]
  /\ nSntYes = 0
  /\ nSntNo  = 0
  /\ nSntYesF = 0
  /\ nSntNoF  = 0
  /\ nRcvdYes = [i \in Proc |-> 0]
  /\ nRcvdNo  = [i \in Proc |-> 0]

InitAllYes ==
  /\ pc = [i \in Proc |-> YES]
  /\ someFail = [i \in Proc |-> FALSE]
  /\ nSntYes = 0
  /\ nSntNo  = 0
  /\ nSntYesF = 0
  /\ nSntNoF  = 0
  /\ nRcvdYes = [i \in Proc |-> 0]
  /\ nRcvdNo  = [i \in Proc |-> 0]

InitSomeNo ==
  /\ InitAny
  /\ \E i \in Proc: pc[i] = NO

CanRecvYes(i) == (nSntYes + nSntYesF) - nRcvdYes[i]
CanRecvNo(i)  == (nSntNo  + nSntNoF)  - nRcvdNo[i]

SendYes(i) ==
  /\ i \in Proc
  /\ pc[i] = YES
  /\ ~someFail[i]                    \* only a non-suspected process broadcasts
  /\ pc' = [pc EXCEPT ![i] = SENT]
  /\ nSntYes' = nSntYes + 1
  /\ UNCHANGED << nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

SendNo(i) ==
  /\ i \in Proc
  /\ pc[i] = NO
  /\ ~someFail[i]                    \* only a non-suspected process broadcasts
  /\ pc' = [pc EXCEPT ![i] = SENT]
  /\ nSntNo' = nSntNo + 1
  /\ UNCHANGED << nSntYes, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

Receive(i) ==
  /\ i \in Proc
  /\ pc[i] = SENT
  /\ LET dy == CanRecvYes(i)
         dn == CanRecvNo(i)
     IN /\ dy \in Nat /\ dn \in Nat
        /\ dy + dn > 0
        /\ nRcvdYes' = [nRcvdYes EXCEPT ![i] = nRcvdYes[i] + dy]
        /\ nRcvdNo'  = [nRcvdNo  EXCEPT ![i] = nRcvdNo[i]  + dn]
  /\ UNCHANGED << pc, nSntYes, nSntNo, nSntYesF, nSntNoF, someFail >>

Commit(i) ==
  /\ i \in Proc
  /\ pc[i] = SENT
  /\ nRcvdYes[i] = N
  /\ nRcvdNo[i]  = 0
  /\ pc' = [pc EXCEPT ![i] = COMMIT]
  /\ UNCHANGED << someFail, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo >>

AbortSent(i) ==
  /\ i \in Proc
  /\ pc[i] = SENT
  /\ nRcvdNo[i] > 0
  /\ pc' = [pc EXCEPT ![i] = ABORT]
  /\ UNCHANGED << someFail, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo >>

AbortNoYes(i) ==
  /\ i \in Proc
  /\ pc[i] \in {YES, NO}
  /\ \E j \in Proc: someFail[j]      \* if any process is suspected, abort before sending
  /\ pc' = [pc EXCEPT ![i] = ABORT]
  /\ UNCHANGED << someFail, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo >>

Crash(i) ==
  /\ i \in Proc
  /\ pc[i] # BYZ
  /\ ~someFail[i]                    \* perfect FD: not suspected before the actual crash
  /\ pc' = [pc EXCEPT ![i] = BYZ]
  /\ someFail' = [someFail EXCEPT ![i] = TRUE]
  /\ IF pc[i] = YES THEN
       /\ nSntYesF' = nSntYesF + 1
       /\ UNCHANGED nSntNoF
     ELSE IF pc[i] = NO THEN
       /\ nSntNoF' = nSntNoF + 1
       /\ UNCHANGED nSntYesF
     ELSE
       /\ UNCHANGED << nSntYesF, nSntNoF >>
  /\ UNCHANGED << nSntYes, nSntNo, nRcvdYes, nRcvdNo >>

Stutter ==
  /\ UNCHANGED Vars

Next ==
  \E i \in Proc:
      \/ SendYes(i)
      \/ SendNo(i)
      \/ Receive(i)
      \/ Commit(i)
      \/ AbortSent(i)
      \/ AbortNoYes(i)
      \/ Crash(i)

WFNonCrash ==
  /\ \A i \in Proc: WF_Vars(SendYes(i))
  /\ \A i \in Proc: WF_Vars(SendNo(i))
  /\ \A i \in Proc: WF_Vars(Receive(i))
  /\ \A i \in Proc: WF_Vars(Commit(i))
  /\ \A i \in Proc: WF_Vars(AbortSent(i))
  /\ \A i \in Proc: WF_Vars(AbortNoYes(i))

Spec ==
  /\ InitAny
  /\ [][Next]_Vars
  /\ WFNonCrash

SpecYes ==
  /\ InitAllYes
  /\ [][Next]_Vars
  /\ WFNonCrash

SpecNo ==
  /\ InitSomeNo
  /\ [][Next]_Vars
  /\ WFNonCrash

AgrrLtl ==
  [](~(\E i \in Proc: \E j \in Proc: pc[i] = COMMIT /\ pc[j] = ABORT))

AbortValidityLtl ==
  [](~(\E i \in Proc: pc[i] = COMMIT))

CommitValidityLtl ==
  [](~(\E i \in Proc: pc[i] = ABORT))

TerminationLtl ==
  ([](\A j \in Proc: ~someFail[j])) => (<>(\A i \in Proc: Decided(i)))

====
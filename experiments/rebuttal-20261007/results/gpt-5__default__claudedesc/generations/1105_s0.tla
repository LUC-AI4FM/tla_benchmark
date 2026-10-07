----------------------------- MODULE NBACCounter -----------------------------
EXTENDS Naturals, TLC

(*
  Counter-abstraction NBAC with a perfect failure detector.
  Instantiated to N = 3 processes.
*)

CONSTANTS N, YES, NO, SENT, ABORT, COMMIT, BYZ

ASSUME N = 3

Proc == 1..N

VARIABLES
  pc,           \* process control state: YES, NO, SENT, ABORT, COMMIT, BYZ
  vote,         \* initial votes YES/NO
  nSntYes,      \* # of YES broadcasts performed by correct (non-faulty-at-send) processes
  nSntNo,       \* # of NO broadcasts performed by correct (non-faulty-at-send) processes
  nSntYesF,     \* upper bound on # of YES broadcasts that may have been (partially) sent by faulty senders
  nSntNoF,      \* upper bound on # of NO broadcasts that may have been (partially) sent by faulty senders
  nRcvdYes,     \* per-process # of YES messages received
  nRcvdNo,      \* per-process # of NO messages received
  someFail      \* perfect failure detector outputs: suspected iff truly crashed
vars == << pc, vote, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

YesBound == nSntYes + nSntYesF
NoBound  == nSntNo  + nSntNoF

TypeOK ==
  /\ pc \in [Proc -> {YES, NO, SENT, ABORT, COMMIT, BYZ}]
  /\ vote \in [Proc -> {YES, NO}]
  /\ nSntYes \in Nat /\ nSntNo \in Nat /\ nSntYesF \in Nat /\ nSntNoF \in Nat
  /\ nRcvdYes \in [Proc -> Nat] /\ nRcvdNo \in [Proc -> Nat]
  /\ someFail \in [Proc -> BOOLEAN]
  /\ \A i \in Proc:
       /\ nRcvdYes[i] <= YesBound
       /\ nRcvdNo[i]  <= NoBound
       /\ nRcvdYes[i] + nRcvdNo[i] <= N
  /\ nSntYes + nSntNo + nSntYesF + nSntNoF <= N

PerfectFD ==
  \A i \in Proc : someFail[i] = (pc[i] = BYZ)

(****************************************************************)
(* Initialization                                                *)
(****************************************************************)

BaseInit ==
  /\ vote \in [Proc -> {YES, NO}]
  /\ pc = vote
  /\ nSntYes = 0 /\ nSntNo = 0 /\ nSntYesF = 0 /\ nSntNoF = 0
  /\ nRcvdYes = [i \in Proc |-> 0]
  /\ nRcvdNo  = [i \in Proc |-> 0]
  /\ someFail = [i \in Proc |-> FALSE]

InitYes ==
  /\ BaseInit
  /\ \A i \in Proc : vote[i] = YES

InitNo ==
  /\ BaseInit
  /\ \E i \in Proc : vote[i] = NO

Init == BaseInit

(****************************************************************)
(* Actions                                                       *)
(****************************************************************)

NoSuspect == \A j \in Proc : ~someFail[j]

SendYes(i) ==
  /\ i \in Proc
  /\ pc[i] = YES
  /\ NoSuspect
  /\ pc' = [pc EXCEPT ![i] = SENT]
  /\ nSntYes' = nSntYes + 1
  /\ UNCHANGED << vote, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

SendNo(i) ==
  /\ i \in Proc
  /\ pc[i] = NO
  /\ NoSuspect
  /\ pc' = [pc EXCEPT ![i] = SENT]
  /\ nSntNo' = nSntNo + 1
  /\ UNCHANGED << vote, nSntYes, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

ReceiveYes(i) ==
  /\ i \in Proc
  /\ pc[i] = SENT
  /\ nRcvdYes[i] < YesBound
  /\ nRcvdYes' = [nRcvdYes EXCEPT ![i] = @ + 1]
  /\ UNCHANGED << pc, vote, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdNo, someFail >>

ReceiveNo(i) ==
  /\ i \in Proc
  /\ pc[i] = SENT
  /\ nRcvdNo[i] < NoBound
  /\ nRcvdNo' = [nRcvdNo EXCEPT ![i] = @ + 1]
  /\ UNCHANGED << pc, vote, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, someFail >>

Commit(i) ==
  /\ i \in Proc
  /\ pc[i] = SENT
  /\ nRcvdYes[i] = N
  /\ nRcvdNo[i] = 0
  /\ pc' = [pc EXCEPT ![i] = COMMIT]
  /\ UNCHANGED << vote, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

AbortSent(i) ==
  /\ i \in Proc
  /\ pc[i] = SENT
  /\ nRcvdNo[i] > 0
  /\ pc' = [pc EXCEPT ![i] = ABORT]
  /\ UNCHANGED << vote, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

AbortNoYes(i) ==
  /\ i \in Proc
  /\ pc[i] \in {YES, NO}
  /\ \E j \in Proc : someFail[j]
  /\ pc' = [pc EXCEPT ![i] = ABORT]
  /\ UNCHANGED << vote, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

Crash(i) ==
  /\ i \in Proc
  /\ pc[i] # BYZ
  /\ pc' = [pc EXCEPT ![i] = BYZ]
  /\ someFail' = [someFail EXCEPT ![i] = TRUE]
  /\ nSntYesF' = nSntYesF + IF pc[i] = YES THEN 1 ELSE 0
  /\ nSntNoF'  = nSntNoF  + IF pc[i] = NO  THEN 1 ELSE 0
  /\ UNCHANGED << vote, nSntYes, nSntNo, nRcvdYes, nRcvdNo >>

Receive(i) == ReceiveYes(i) \/ ReceiveNo(i)

Next ==
  \E i \in Proc :
    SendYes(i) \/ SendNo(i) \/ Receive(i) \/
    Commit(i)  \/ AbortSent(i) \/ AbortNoYes(i) \/
    Crash(i)

(****************************************************************)
(* Fairness                                                      *)
(****************************************************************)

Fair ==
  /\ \A i \in Proc : WF_vars(SendYes(i))
  /\ \A i \in Proc : WF_vars(SendNo(i))
  /\ \A i \in Proc : WF_vars(ReceiveYes(i))
  /\ \A i \in Proc : WF_vars(ReceiveNo(i))
  /\ \A i \in Proc : WF_vars(Commit(i))
  /\ \A i \in Proc : WF_vars(AbortSent(i))
  /\ \A i \in Proc : WF_vars(AbortNoYes(i))

Spec    == Init    /\ [][Next]_vars /\ Fair
SpecYes == InitYes /\ [][Next]_vars /\ Fair
SpecNo  == InitNo  /\ [][Next]_vars /\ Fair

(****************************************************************)
(* Properties                                                    *)
(****************************************************************)

Agreement ==
  []( \A i, j \in Proc : ~(pc[i] = COMMIT /\ pc[j] = ABORT) )

AbortValidity ==
  ( \E i \in Proc : vote[i] = NO ) => [] ( \A j \in Proc : pc[j] # COMMIT )

CommitValidity ==
  ( (\A i \in Proc : vote[i] = YES) /\ [](\A j \in Proc : ~someFail[j]) )
     => [] ( \A k \in Proc : pc[k] # ABORT )

NoCrash == \A i \in Proc : pc[i] # BYZ
AllDecided == \A i \in Proc : pc[i] \in {COMMIT, ABORT}

Termination ==
  (NoCrash /\ NoSuspect) ~> AllDecided

TypeOKInv == []TypeOK
PerfectFDInv == []PerfectFD

=============================================================================
--------------------------- MODULE nbacg_guer01 ---------------------------
(***************************************************************************)
(* Counter-abstraction model of Non-Blocking Atomic Commitment (NBAC)      *)
(* with failure detectors, after Guerraoui (2001).                         *)
(* Votes sent by correct processes are counted in nSntYes / nSntNo.        *)
(* Votes that crashed processes may have sent are bounded by nSntYesF and  *)
(* nSntNoF. someFail models a perfect failure detector.                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N = 3

VARIABLES
  pc,         \* local status of each process
  nSntYes,    \* YES votes sent by correct processes
  nSntNo,     \* NO votes sent by correct processes
  nSntYesF,   \* bound on YES votes possibly sent by faulty processes
  nSntNoF,    \* bound on NO votes possibly sent by faulty processes
  nRcvdYes,   \* per-process number of received YES votes
  nRcvdNo,    \* per-process number of received NO votes
  someFail    \* perfect failure detector output per process

vars == << pc, nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

Proc == 1..N

Status == { "YES", "NO", "SENT", "ABORT", "COMMIT", "BYZ" }

TypeOK ==
  /\ pc \in [ Proc -> Status ]
  /\ nSntYes \in 0..N
  /\ nSntNo \in 0..N
  /\ nSntYesF \in 0..N
  /\ nSntNoF \in 0..N
  /\ nRcvdYes \in [ Proc -> 0..N ]
  /\ nRcvdNo \in [ Proc -> 0..N ]
  /\ someFail \in [ Proc -> BOOLEAN ]

CommonInit ==
  /\ nSntYes = 0
  /\ nSntNo = 0
  /\ nSntYesF = 0
  /\ nSntNoF = 0
  /\ nRcvdYes = [ i \in Proc |-> 0 ]
  /\ nRcvdNo = [ i \in Proc |-> 0 ]
  /\ someFail = [ i \in Proc |-> FALSE ]

Init ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ CommonInit

InitYes ==
  /\ pc = [ i \in Proc |-> "YES" ]
  /\ CommonInit

InitNo ==
  /\ pc \in [ Proc -> { "YES", "NO" } ]
  /\ \E i \in Proc : pc[i] = "NO"
  /\ CommonInit

(* A non-suspected process broadcasts its YES vote *)
SendYes(i) ==
  /\ pc[i] = "YES"
  /\ ~someFail[i]
  /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
  /\ nSntYes' = nSntYes + 1
  /\ UNCHANGED << nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

(* A non-suspected process broadcasts its NO vote *)
SendNo(i) ==
  /\ pc[i] = "NO"
  /\ ~someFail[i]
  /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
  /\ nSntNo' = nSntNo + 1
  /\ UNCHANGED << nSntYes, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

(* A SENT process receives one more message *)
Receive(i) ==
  /\ pc[i] = "SENT"
  /\ \/ /\ nRcvdYes[i] < nSntYes + nSntYesF
        /\ nRcvdYes' = [ nRcvdYes EXCEPT ![i] = nRcvdYes[i] + 1 ]
        /\ UNCHANGED nRcvdNo
     \/ /\ nRcvdNo[i] < nSntNo + nSntNoF
        /\ nRcvdNo' = [ nRcvdNo EXCEPT ![i] = nRcvdNo[i] + 1 ]
        /\ UNCHANGED nRcvdYes
  /\ UNCHANGED << pc, nSntYes, nSntNo, nSntYesF, nSntNoF, someFail >>

(* Commit after receiving N YES votes and no NO vote *)
Commit(i) ==
  /\ pc[i] = "SENT"
  /\ nRcvdYes[i] >= N
  /\ nRcvdNo[i] = 0
  /\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
  /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

(* Abort after receiving some NO vote *)
AbortSent(i) ==
  /\ pc[i] = "SENT"
  /\ nRcvdNo[i] > 0
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

(* A process that suspects a failure aborts before sending its vote *)
AbortNoYes(i) ==
  /\ pc[i] \in { "YES", "NO" }
  /\ someFail[i]
  /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
  /\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

(* A process crashes; the perfect failure detector reports it *)
Crash(i) ==
  /\ pc[i] # "BYZ"
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
  /\ someFail' = [ j \in Proc |-> TRUE ]
  /\ nSntYesF' = IF pc[i] = "YES" THEN nSntYesF + 1 ELSE nSntYesF
  /\ nSntNoF' = IF pc[i] = "NO" THEN nSntNoF + 1 ELSE nSntNoF
  /\ UNCHANGED << nSntYes, nSntNo, nRcvdYes, nRcvdNo >>

NonCrashStep ==
  \E i \in Proc :
    \/ SendYes(i)
    \/ SendNo(i)
    \/ Receive(i)
    \/ Commit(i)
    \/ AbortSent(i)
    \/ AbortNoYes(i)

Next ==
  \/ NonCrashStep
  \/ \E i \in Proc : Crash(i)
  \/ UNCHANGED vars

Spec    == Init    /\ [][Next]_vars /\ WF_vars(NonCrashStep)
SpecYes == InitYes /\ [][Next]_vars /\ WF_vars(NonCrashStep)
SpecNo  == InitNo  /\ [][Next]_vars /\ WF_vars(NonCrashStep)

(* Properties *)

Agreement ==
  [](\A i, j \in Proc : ~(pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

AbortValidity ==
  (\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

CommitValidity ==
  ( /\ \A i \in Proc : pc[i] = "YES"
    /\ [](\A i \in Proc : ~someFail[i]) )
    => [](\A i \in Proc : pc[i] # "ABORT")

Termination ==
  [](\A i \in Proc : pc[i] # "BYZ" /\ ~someFail[i])
    => <>(\A i \in Proc : pc[i] \in { "COMMIT", "ABORT" })

=============================================================================
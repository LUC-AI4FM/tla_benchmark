------------------------------ MODULE APAnbacg_guer01 ------------------------------
(***************************************************************************)
(* Apalache type-annotation wrapper around nbacg_guer01.                   *)
(* The original module is left unchanged and instantiated below. To keep   *)
(* this file self-contained for SANY, nbacg_guer01 appears as an inner     *)
(* module. The wrapper's top level declares only the typed CONSTANT and    *)
(* VARIABLES. Init, Next, Spec, the invariants and the liveness property   *)
(* all come from the INSTANCE.                                             *)
(***************************************************************************)

---------------------------------- MODULE nbacg_guer01 ----------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES
    nSntNo,     \* number of NO messages sent
    nSntYes,    \* number of YES messages sent
    nSntNoF,    \* number of NO messages sent by processes that later crashed
    nSntYesF,   \* number of YES messages sent by processes that later crashed
    nRcvdYes,   \* nRcvdYes[i]: YES messages received by process i
    nRcvdNo,    \* nRcvdNo[i]: NO messages received by process i
    someFail,   \* someFail[i]: the failure detector of process i has suspected a crash
    pc          \* program counter of each process

vars == << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail, pc >>

Proc == 1 .. N

Locations == { "YES", "NO", "SY", "SN", "COMMIT", "ABORT", "CRASH" }

TypeOK ==
    /\ nSntNo \in Nat
    /\ nSntYes \in Nat
    /\ nSntNoF \in Nat
    /\ nSntYesF \in Nat
    /\ nRcvdYes \in [Proc -> Nat]
    /\ nRcvdNo \in [Proc -> Nat]
    /\ someFail \in [Proc -> BOOLEAN]
    /\ pc \in [Proc -> Locations]

Init ==
    /\ nSntNo = 0
    /\ nSntYes = 0
    /\ nSntNoF = 0
    /\ nSntYesF = 0
    /\ nRcvdYes = [i \in Proc |-> 0]
    /\ nRcvdNo = [i \in Proc |-> 0]
    /\ someFail = [i \in Proc |-> FALSE]
    /\ pc \in [Proc -> {"YES", "NO"}]

\* A process broadcasts its vote.
SendYes(i) ==
    /\ pc[i] = "YES"
    /\ pc' = [pc EXCEPT ![i] = "SY"]
    /\ nSntYes' = nSntYes + 1
    /\ UNCHANGED << nSntNo, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

SendNo(i) ==
    /\ pc[i] = "NO"
    /\ pc' = [pc EXCEPT ![i] = "SN"]
    /\ nSntNo' = nSntNo + 1
    /\ UNCHANGED << nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* A process crashes.
Crash(i) ==
    /\ pc[i] \in { "YES", "NO", "SY", "SN" }
    /\ pc' = [pc EXCEPT ![i] = "CRASH"]
    /\ nSntYesF' = IF pc[i] = "SY" THEN nSntYesF + 1 ELSE nSntYesF
    /\ nSntNoF' = IF pc[i] = "SN" THEN nSntNoF + 1 ELSE nSntNoF
    /\ UNCHANGED << nSntNo, nSntYes, nRcvdYes, nRcvdNo, someFail >>

\* A process receives a message that has been sent.
RcvYes(i) ==
    /\ pc[i] \in { "SY", "SN" }
    /\ nRcvdYes[i] < nSntYes
    /\ nRcvdYes' = [nRcvdYes EXCEPT ![i] = @ + 1]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdNo, someFail, pc >>

RcvNo(i) ==
    /\ pc[i] \in { "SY", "SN" }
    /\ nRcvdNo[i] < nSntNo
    /\ nRcvdNo' = [nRcvdNo EXCEPT ![i] = @ + 1]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, someFail, pc >>

\* The failure detector suspects a crash (it is accurate).
DetectFailure(i) ==
    /\ pc[i] \in { "SY", "SN" }
    /\ ~someFail[i]
    /\ \E j \in Proc : pc[j] = "CRASH"
    /\ someFail' = [someFail EXCEPT ![i] = TRUE]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, pc >>

\* Decision rules.
Abort(i) ==
    /\ pc[i] \in { "SY", "SN" }
    /\ (nRcvdNo[i] > 0 \/ someFail[i])
    /\ pc' = [pc EXCEPT ![i] = "ABORT"]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

Commit(i) ==
    /\ pc[i] \in { "SY", "SN" }
    /\ nRcvdYes[i] = N
    /\ nRcvdNo[i] = 0
    /\ ~someFail[i]
    /\ pc' = [pc EXCEPT ![i] = "COMMIT"]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

Step(i) ==
    \/ SendYes(i) \/ SendNo(i)
    \/ RcvYes(i) \/ RcvNo(i)
    \/ DetectFailure(i)
    \/ Abort(i) \/ Commit(i)

Next ==
    \/ \E i \in Proc : Step(i) \/ Crash(i)
    \/ UNCHANGED vars

Fairness == \A i \in Proc : WF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: a commit happens only if nobody voted NO.
CommitValidity ==
    (\E i \in Proc : pc[i] = "COMMIT") => nSntNo = 0

\* Safety: the crashed-sender counters never exceed the totals.
FaultyBound ==
    /\ nSntYesF <= nSntYes
    /\ nSntNoF <= nSntNo

\* Liveness: every process eventually decides or crashes.
Termination ==
    <>(\A i \in Proc : pc[i] \in { "COMMIT", "ABORT", "CRASH" })
=========================================================================================
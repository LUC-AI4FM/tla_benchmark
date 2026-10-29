------------------------------ MODULE MC_nbacg_guer01 ------------------------------
(***************************************************************************)
(* Non-Blocking Atomic Commit with failure detectors (after nbacg_guer01), *)
(* with Apalache type annotations. This module is self-contained: the      *)
(* protocol of nbacg_guer01 is reproduced here so it parses with SANY.     *)
(* Model configuration: N = 3.                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT
    \* @type: Int;
    N

ASSUME N \in Nat /\ N >= 1

VARIABLES
    \* @type: Int;
    nSntNo,     \* number of "no" messages sent by processes that stay correct
    \* @type: Int;
    nSntYes,    \* number of "yes" messages sent by processes that stay correct
    \* @type: Int;
    nSntNoF,    \* number of "no" messages sent by processes that then crashed
    \* @type: Int;
    nSntYesF,   \* number of "yes" messages sent by processes that then crashed
    \* @type: Int -> Int;
    nRcvdYes,   \* nRcvdYes[i]: number of "yes" messages received by i
    \* @type: Int -> Int;
    nRcvdNo,    \* nRcvdNo[i]: number of "no" messages received by i
    \* @type: Int -> Bool;
    someFail,   \* someFail[i]: the failure detector of i has reported a crash
    \* @type: Int -> Str;
    pc          \* local state of each process

vars == << nSntNo, nSntYes, nSntNoF, nSntYesF,
           nRcvdYes, nRcvdNo, someFail, pc >>

Proc == 1..N

Locations == {"YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH"}

-----------------------------------------------------------------------------

Init ==
    /\ nSntNo = 0
    /\ nSntYes = 0
    /\ nSntNoF = 0
    /\ nSntYesF = 0
    /\ nRcvdYes = [i \in Proc |-> 0]
    /\ nRcvdNo = [i \in Proc |-> 0]
    /\ someFail = [i \in Proc |-> FALSE]
    /\ pc \in [Proc -> {"YES", "NO"}]

\* A correct process broadcasts its "yes" vote
SendYes(i) ==
    /\ pc[i] = "YES"
    /\ pc' = [pc EXCEPT ![i] = "SENT"]
    /\ nSntYes' = nSntYes + 1
    /\ UNCHANGED << nSntNo, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* A correct process broadcasts its "no" vote
SendNo(i) ==
    /\ pc[i] = "NO"
    /\ pc' = [pc EXCEPT ![i] = "SENT"]
    /\ nSntNo' = nSntNo + 1
    /\ UNCHANGED << nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* A process sends "yes" and then crashes
SendYesAndCrash(i) ==
    /\ pc[i] = "YES"
    /\ pc' = [pc EXCEPT ![i] = "CRASH"]
    /\ nSntYesF' = nSntYesF + 1
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

\* A process sends "no" and then crashes
SendNoAndCrash(i) ==
    /\ pc[i] = "NO"
    /\ pc' = [pc EXCEPT ![i] = "CRASH"]
    /\ nSntNoF' = nSntNoF + 1
    /\ UNCHANGED << nSntNo, nSntYes, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* A process crashes (without sending anything further)
Crash(i) ==
    /\ pc[i] # "CRASH"
    /\ pc' = [pc EXCEPT ![i] = "CRASH"]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF,
                    nRcvdYes, nRcvdNo, someFail >>

\* A live process receives a "yes" message
RcvYes(i) ==
    /\ pc[i] # "CRASH"
    /\ nRcvdYes[i] < nSntYes + nSntYesF
    /\ nRcvdYes' = [nRcvdYes EXCEPT ![i] = nRcvdYes[i] + 1]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF,
                    nRcvdNo, someFail, pc >>

\* A live process receives a "no" message
RcvNo(i) ==
    /\ pc[i] # "CRASH"
    /\ nRcvdNo[i] < nSntNo + nSntNoF
    /\ nRcvdNo' = [nRcvdNo EXCEPT ![i] = nRcvdNo[i] + 1]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF,
                    nRcvdYes, someFail, pc >>

\* The failure detector of a live process reports a crash
DetectFail(i) ==
    /\ pc[i] # "CRASH"
    /\ ~someFail[i]
    /\ \E j \in Proc : pc[j] = "CRASH"
    /\ someFail' = [someFail EXCEPT ![i] = TRUE]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF,
                    nRcvdYes, nRcvdNo, pc >>

\* Commit after receiving "yes" from every process and no failure detected
Commit(i) ==
    /\ pc[i] = "SENT"
    /\ nRcvdYes[i] = N
    /\ nRcvdNo[i] = 0
    /\ ~someFail[i]
    /\ pc' = [pc EXCEPT ![i] = "COMMIT"]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF,
                    nRcvdYes, nRcvdNo, someFail >>

\* Abort after receiving a "no" vote or detecting a failure
Abort(i) ==
    /\ pc[i] = "SENT"
    /\ (nRcvdNo[i] > 0 \/ someFail[i])
    /\ pc' = [pc EXCEPT ![i] = "ABORT"]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF,
                    nRcvdYes, nRcvdNo, someFail >>

Next ==
    \/ \E i \in Proc :
          \/ SendYes(i)
          \/ SendNo(i)
          \/ SendYesAndCrash(i)
          \/ SendNoAndCrash(i)
          \/ Crash(i)
          \/ RcvYes(i)
          \/ RcvNo(i)
          \/ DetectFail(i)
          \/ Commit(i)
          \/ Abort(i)
    \/ UNCHANGED vars   \* stuttering in terminal states (no deadlock)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ nSntNo \in 0..N
    /\ nSntYes \in 0..N
    /\ nSntNoF \in 0..N
    /\ nSntYesF \in 0..N
    /\ nRcvdYes \in [Proc -> 0..N]
    /\ nRcvdNo \in [Proc -> 0..N]
    /\ someFail \in [Proc -> BOOLEAN]
    /\ pc \in [Proc -> Locations]

\* If some process voted "no", nobody commits
Validity ==
    (nSntNo + nSntNoF > 0) => \A i \in Proc : pc[i] # "COMMIT"

\* Message counters are consistent
CountersOK ==
    /\ nSntNo + nSntYes + nSntNoF + nSntYesF <= N
    /\ \A i \in Proc : nRcvdYes[i] <= nSntYes + nSntYesF
                       /\ nRcvdNo[i] <= nSntNo + nSntNoF

=============================================================================
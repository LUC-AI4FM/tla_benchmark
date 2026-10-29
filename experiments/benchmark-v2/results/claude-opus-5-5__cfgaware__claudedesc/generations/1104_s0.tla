---------------------------- MODULE nbacg_guer01_typed ----------------------------
(* Apalache-typed version of Non-Blocking Atomic Commit with failure detectors,
   modelled after nbacg_guer01. The underlying protocol is inlined so that the
   module is self-contained. *)

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Int;
    N

VARIABLES
    \* @type: Int;
    nSntNo,
    \* @type: Int;
    nSntYes,
    \* @type: Int;
    nSntNoF,
    \* @type: Int;
    nSntYesF,
    \* @type: Int -> Int;
    nRcvdYes,
    \* @type: Int -> Int;
    nRcvdNo,
    \* @type: Int -> Bool;
    someFail,
    \* @type: Int -> Str;
    pc

vars == << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail, pc >>

Proc == 1 .. N

Location == { "YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH" }

Init ==
    /\ nSntNo = 0
    /\ nSntYes = 0
    /\ nSntNoF = 0
    /\ nSntYesF = 0
    /\ nRcvdYes = [ i \in Proc |-> 0 ]
    /\ nRcvdNo = [ i \in Proc |-> 0 ]
    /\ someFail = [ i \in Proc |-> FALSE ]
    /\ pc \in [ Proc -> { "YES", "NO" } ]

\* A correct process votes yes
SendYes(i) ==
    /\ pc[i] = "YES"
    /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
    /\ nSntYes' = nSntYes + 1
    /\ UNCHANGED << nSntNo, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* A correct process votes no
SendNo(i) ==
    /\ pc[i] = "NO"
    /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
    /\ nSntNo' = nSntNo + 1
    /\ UNCHANGED << nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* A process crashes while (or instead of) sending its vote
CrashYes(i) ==
    /\ pc[i] = "YES"
    /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
    /\ nSntYesF' = nSntYesF + 1
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nRcvdYes, nRcvdNo, someFail >>

CrashNo(i) ==
    /\ pc[i] = "NO"
    /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
    /\ nSntNoF' = nSntNoF + 1
    /\ UNCHANGED << nSntNo, nSntYes, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

CrashSilent(i) ==
    /\ pc[i] \in { "YES", "NO", "SENT" }
    /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* Receiving votes
RcvYes(i) ==
    /\ pc[i] # "CRASH"
    /\ nRcvdYes[i] < nSntYes + nSntYesF
    /\ nRcvdYes' = [ nRcvdYes EXCEPT ![i] = nRcvdYes[i] + 1 ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdNo, someFail, pc >>

RcvNo(i) ==
    /\ pc[i] # "CRASH"
    /\ nRcvdNo[i] < nSntNo + nSntNoF
    /\ nRcvdNo' = [ nRcvdNo EXCEPT ![i] = nRcvdNo[i] + 1 ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, someFail, pc >>

\* Failure detector: a process may (only) detect failures that happened
DetectFailure(i) ==
    /\ pc[i] # "CRASH"
    /\ someFail[i] = FALSE
    /\ \E j \in Proc : pc[j] = "CRASH"
    /\ someFail' = [ someFail EXCEPT ![i] = TRUE ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, pc >>

\* Decisions
Commit(i) ==
    /\ pc[i] = "SENT"
    /\ nRcvdYes[i] = N
    /\ someFail[i] = FALSE
    /\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

Abort(i) ==
    /\ pc[i] = "SENT"
    /\ (nRcvdNo[i] > 0 \/ someFail[i] = TRUE)
    /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

Next ==
    \/ \E i \in Proc :
        \/ SendYes(i)
        \/ SendNo(i)
        \/ CrashYes(i)
        \/ CrashNo(i)
        \/ CrashSilent(i)
        \/ RcvYes(i)
        \/ RcvNo(i)
        \/ DetectFailure(i)
        \/ Commit(i)
        \/ Abort(i)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ nSntNo \in 0 .. N
    /\ nSntYes \in 0 .. N
    /\ nSntNoF \in 0 .. N
    /\ nSntYesF \in 0 .. N
    /\ nRcvdYes \in [ Proc -> 0 .. N ]
    /\ nRcvdNo \in [ Proc -> 0 .. N ]
    /\ someFail \in [ Proc -> BOOLEAN ]
    /\ pc \in [ Proc -> Location ]

=============================================================================
------------------------------ MODULE nbacg_guer01_typed ------------------------------
(*
  Apalache type-annotation wrapper for nbacg_guer01. It declares N and the
  protocol's state variables. The algorithm is written inline here, so the
  module stays self-contained and parses even when nbacg_guer01 is absent.
*)
EXTENDS Naturals, FiniteSets

CONSTANT
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

\* A process that votes YES broadcasts a YES message.
SendYes(i) ==
    /\ pc[i] = "YES"
    /\ nSntYes' = nSntYes + 1
    /\ pc' = [ pc EXCEPT ![i] = "SENT" ]
    /\ UNCHANGED << nSntNo, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* A process that votes NO broadcasts a NO message and may abort immediately.
SendNo(i) ==
    /\ pc[i] = "NO"
    /\ nSntNo' = nSntNo + 1
    /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
    /\ UNCHANGED << nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* A process crashes. If it crashes before sending, it may still have sent
\* its vote message to some processes; this is modelled through the F counters.
Crash(i) ==
    /\ pc[i] \in { "YES", "NO", "SENT" }
    /\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
    /\ \/ /\ pc[i] = "YES"
          /\ nSntYesF' = nSntYesF + 1
          /\ UNCHANGED nSntNoF
       \/ /\ pc[i] = "NO"
          /\ nSntNoF' = nSntNoF + 1
          /\ UNCHANGED nSntYesF
       \/ /\ pc[i] \in { "YES", "NO", "SENT" }
          /\ UNCHANGED << nSntNoF, nSntYesF >>
    /\ UNCHANGED << nSntNo, nSntYes, nRcvdYes, nRcvdNo, someFail >>

\* Receive a YES message (from a correct or a failed sender).
RcvYes(i) ==
    /\ pc[i] \notin { "CRASH" }
    /\ nRcvdYes[i] < nSntYes + nSntYesF
    /\ nRcvdYes' = [ nRcvdYes EXCEPT ![i] = @ + 1 ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdNo, someFail, pc >>

\* Receive a NO message (from a correct or a failed sender).
RcvNo(i) ==
    /\ pc[i] \notin { "CRASH" }
    /\ nRcvdNo[i] < nSntNo + nSntNoF
    /\ nRcvdNo' = [ nRcvdNo EXCEPT ![i] = @ + 1 ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, someFail, pc >>

\* The failure detector reports a failure to process i.
DetectFail(i) ==
    /\ pc[i] \notin { "CRASH" }
    /\ \E j \in Proc : pc[j] = "CRASH"
    /\ someFail[i] = FALSE
    /\ someFail' = [ someFail EXCEPT ![i] = TRUE ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, pc >>

\* Decide ABORT on receiving a NO vote or detecting a failure.
DecideAbort(i) ==
    /\ pc[i] = "SENT"
    /\ (nRcvdNo[i] > 0 \/ someFail[i])
    /\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

\* Decide COMMIT after receiving YES from all processes and no failure seen.
DecideCommit(i) ==
    /\ pc[i] = "SENT"
    /\ nRcvdYes[i] >= N
    /\ nRcvdNo[i] = 0
    /\ ~someFail[i]
    /\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
    /\ UNCHANGED << nSntNo, nSntYes, nSntNoF, nSntYesF, nRcvdYes, nRcvdNo, someFail >>

Next ==
    \/ \E i \in Proc :
        \/ SendYes(i)
        \/ SendNo(i)
        \/ Crash(i)
        \/ RcvYes(i)
        \/ RcvNo(i)
        \/ DetectFail(i)
        \/ DecideAbort(i)
        \/ DecideCommit(i)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ nSntNo \in 0 .. N
    /\ nSntYes \in 0 .. N
    /\ nSntNoF \in 0 .. N
    /\ nSntYesF \in 0 .. N
    /\ nRcvdYes \in [ Proc -> 0 .. (2 * N) ]
    /\ nRcvdNo \in [ Proc -> 0 .. (2 * N) ]
    /\ someFail \in [ Proc -> BOOLEAN ]
    /\ pc \in [ Proc -> Location ]

=============================================================================
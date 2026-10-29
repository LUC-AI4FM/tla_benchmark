---------------------------- MODULE APAnbacg_guer01 ----------------------------
(***************************************************************************)
(* Apalache type-annotation wrapper for the non-blocking atomic commitment *)
(* protocol nbacg_guer01 (Guerraoui's NBAC with a failure detector).       *)
(*                                                                         *)
(* The original wrapper declares the typed constant N and the typed state  *)
(* variables, then writes                                                  *)
(*      INSTANCE nbacg_guer01                                              *)
(* so that the original module stays unchanged. The wrapped module may not *)
(* be available to SANY. To keep this file standalone and parseable, the   *)
(* body of the wrapped protocol is inlined below, over the same typed      *)
(* constants and variables.                                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Int;
    N

ASSUME N \in Nat /\ N >= 1

VARIABLES
    \* @type: Int;
    nSntYes,        \* number of YES votes sent
    \* @type: Int;
    nSntNo,         \* number of NO votes sent
    \* @type: Int;
    nCrash,         \* number of crashed processes
    \* @type: Int -> Int;
    nRcvdYes,       \* YES votes received by each process
    \* @type: Int -> Int;
    nRcvdNo,        \* NO votes received by each process
    \* @type: Int -> Bool;
    someFail,       \* failure-detector flag of each process
    \* @type: Int -> Str;
    pc              \* program counter of each process

vars == <<nSntYes, nSntNo, nCrash, nRcvdYes, nRcvdNo, someFail, pc>>

Proc == 1 .. N

Location == {"YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH"}

Decided(i) == pc[i] \in {"COMMIT", "ABORT"}

TypeOK ==
    /\ nSntYes \in 0 .. N
    /\ nSntNo \in 0 .. N
    /\ nCrash \in 0 .. N
    /\ nRcvdYes \in [Proc -> 0 .. N]
    /\ nRcvdNo \in [Proc -> 0 .. N]
    /\ someFail \in [Proc -> BOOLEAN]
    /\ pc \in [Proc -> Location]

Init ==
    /\ nSntYes = 0
    /\ nSntNo = 0
    /\ nCrash = 0
    /\ nRcvdYes = [i \in Proc |-> 0]
    /\ nRcvdNo = [i \in Proc |-> 0]
    /\ someFail = [i \in Proc |-> FALSE]
    /\ pc \in [Proc -> {"YES", "NO"}]

\* A process broadcasts its YES vote.
SendYes(i) ==
    /\ pc[i] = "YES"
    /\ pc' = [pc EXCEPT ![i] = "SENT"]
    /\ nSntYes' = nSntYes + 1
    /\ UNCHANGED <<nSntNo, nCrash, nRcvdYes, nRcvdNo, someFail>>

\* A process broadcasts its NO vote.
SendNo(i) ==
    /\ pc[i] = "NO"
    /\ pc' = [pc EXCEPT ![i] = "SENT"]
    /\ nSntNo' = nSntNo + 1
    /\ UNCHANGED <<nSntYes, nCrash, nRcvdYes, nRcvdNo, someFail>>

\* A process crashes (messages already sent remain in transit).
Crash(i) ==
    /\ pc[i] \notin {"CRASH"}
    /\ pc' = [pc EXCEPT ![i] = "CRASH"]
    /\ nCrash' = nCrash + 1
    /\ UNCHANGED <<nSntYes, nSntNo, nRcvdYes, nRcvdNo, someFail>>

\* Reception of a YES vote.
RcvYes(i) ==
    /\ pc[i] \notin {"CRASH"}
    /\ nRcvdYes[i] < nSntYes
    /\ nRcvdYes' = [nRcvdYes EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<nSntYes, nSntNo, nCrash, nRcvdNo, someFail, pc>>

\* Reception of a NO vote.
RcvNo(i) ==
    /\ pc[i] \notin {"CRASH"}
    /\ nRcvdNo[i] < nSntNo
    /\ nRcvdNo' = [nRcvdNo EXCEPT ![i] = @ + 1]
    /\ UNCHANGED <<nSntYes, nSntNo, nCrash, nRcvdYes, someFail, pc>>

\* The (perfect) failure detector reports that some process has crashed.
Detect(i) ==
    /\ pc[i] \notin {"CRASH"}
    /\ nCrash > 0
    /\ ~someFail[i]
    /\ someFail' = [someFail EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<nSntYes, nSntNo, nCrash, nRcvdYes, nRcvdNo, pc>>

\* Commit when YES votes from all N processes have been received.
DecideCommit(i) ==
    /\ pc[i] = "SENT"
    /\ nRcvdYes[i] = N
    /\ ~someFail[i]
    /\ pc' = [pc EXCEPT ![i] = "COMMIT"]
    /\ UNCHANGED <<nSntYes, nSntNo, nCrash, nRcvdYes, nRcvdNo, someFail>>

\* Abort upon a NO vote or a suspected failure.
DecideAbort(i) ==
    /\ pc[i] = "SENT"
    /\ (nRcvdNo[i] > 0 \/ someFail[i])
    /\ pc' = [pc EXCEPT ![i] = "ABORT"]
    /\ UNCHANGED <<nSntYes, nSntNo, nCrash, nRcvdYes, nRcvdNo, someFail>>

\* Stuttering once every process has decided or crashed (avoids deadlock).
Done ==
    /\ \A i \in Proc : pc[i] \in {"COMMIT", "ABORT", "CRASH"}
    /\ UNCHANGED vars

Next ==
    \/ \E i \in Proc :
          \/ SendYes(i)
          \/ SendNo(i)
          \/ Crash(i)
          \/ RcvYes(i)
          \/ RcvNo(i)
          \/ Detect(i)
          \/ DecideCommit(i)
          \/ DecideAbort(i)
    \/ Done

\* Fairness: correct processes keep taking steps; crashes are not forced.
Fairness ==
    \A i \in Proc :
        /\ WF_vars(SendYes(i))
        /\ WF_vars(SendNo(i))
        /\ WF_vars(RcvYes(i))
        /\ WF_vars(RcvNo(i))
        /\ WF_vars(Detect(i))
        /\ WF_vars(DecideCommit(i))
        /\ WF_vars(DecideAbort(i))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

\* Commit-Validity: a process commits only if all processes voted YES.
CommitValidity ==
    (\E i \in Proc : pc[i] = "COMMIT") => (nSntYes = N /\ nSntNo = 0)

\* Abort-Validity: a process aborts only if some process voted NO
\* or some process crashed.
AbortValidity ==
    (\E i \in Proc : pc[i] = "ABORT") => (nSntNo > 0 \/ nCrash > 0)

\* Without NO votes and without failures, nobody aborts.
NoAbortWithoutCause ==
    (nSntNo = 0 /\ nCrash = 0) => \A i \in Proc : pc[i] # "ABORT"

\* Once a NO vote was cast, nobody commits.
NoCommitAfterNo ==
    (nSntNo > 0) => \A i \in Proc : pc[i] # "COMMIT"

Safety ==
    /\ TypeOK
    /\ CommitValidity
    /\ AbortValidity
    /\ NoAbortWithoutCause
    /\ NoCommitAfterNo

---------------------------------------------------------------------------
(* Liveness properties *)

\* Termination: every correct process eventually decides.
Termination ==
    <>(\A i \in Proc : pc[i] \in {"COMMIT", "ABORT", "CRASH"})

\* Non-triviality: if all vote YES and nobody fails, all eventually commit.
NonTriviality ==
    ((\A i \in Proc : pc[i] = "YES") /\ [](nCrash = 0))
        => <>(\A i \in Proc : pc[i] = "COMMIT")

=============================================================================
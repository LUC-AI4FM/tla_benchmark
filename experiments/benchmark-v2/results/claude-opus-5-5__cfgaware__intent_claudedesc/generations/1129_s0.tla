------------------------------ MODULE TwoPhase ------------------------------
(***************************************************************************)
(* Two-Phase Commit protocol. A single transaction manager (TM)            *)
(* coordinates a set RM of resource managers. Messages are modeled as a    *)
(* grow-only set msgs of sent messages; a message is received when it      *)
(* is in msgs.                                                             *)
(***************************************************************************)
CONSTANT RM   \* The set of resource managers

VARIABLES
  rmState,    \* rmState[r] is the state of resource manager r
  tmState,    \* The state of the transaction manager
  tmPrepared, \* The set of RMs from which the TM has received "Prepared"
  msgs        \* The set of all messages that have been sent

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages ==
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]

TPTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

TPInit ==
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(* Transaction manager actions *)

TMRcvPrepared(r) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

(* Resource manager actions *)

RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>

RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E r \in RM :
       TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
         \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)

TPSpec == TPInit /\ [][TPNext]_vars

-----------------------------------------------------------------------------
(* Transaction Commit correctness conditions *)

TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

CommitOnlyIfAllPrepared ==
  (\E r \in RM : rmState[r] = "committed") =>
     \A r \in RM : rmState[r] \in {"prepared", "committed"}

TCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]

TCPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}
notCommitted == \A r \in RM : rmState[r] # "committed"

TCDecide(r) ==
  \/ /\ rmState[r] = "prepared"
     /\ canCommit
     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  \/ /\ rmState[r] \in {"working", "prepared"}
     /\ notCommitted
     /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : TCPrepare(r) \/ TCDecide(r)

TCSpec == TCInit /\ [][TCNext]_rmState

THEOREM TPSpec => [](TPTypeOK /\ TCConsistent)
THEOREM TPSpec => TCSpec
=============================================================================
------------------------------ MODULE TwoPhase ------------------------------
(***************************************************************************)
(* Two-Phase Commit protocol.  A transaction manager (TM) coordinates a    *)
(* set of resource managers (RMs).  Simplifications:                       *)
(*  - RMs spontaneously send "Prepared" messages; TM "Prepare" messages    *)
(*    are not modeled.                                                     *)
(*  - RMs do not send "Abort" messages to the TM; the TM may spontaneously *)
(*    decide to abort.                                                     *)
(*  - Only safety is specified; no liveness or fairness.                   *)
(*  - Messages are kept in a set of sent messages and are never lost or    *)
(*    removed.                                                             *)
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
       \/ TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
       \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)

TPSpec == TPInit /\ [][TPNext]_vars

Init == TPInit
Next == TPNext
Spec == TPSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* The higher-level Transaction Commit specification (TCommit), defined    *)
(* over rmState, which Two-Phase Commit implements.                        *)
(***************************************************************************)
TCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed"

TCPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

TCDecide(r) ==
  \/ /\ rmState[r] = "prepared"
     /\ canCommit
     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  \/ /\ rmState[r] \in {"working", "prepared"}
     /\ notCommitted
     /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : TCPrepare(r) \/ TCDecide(r)

TCSpec == TCInit /\ [][TCNext]_rmState

TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

-----------------------------------------------------------------------------
(* Safety properties *)

THEOREM TPSpec => [](TPTypeOK /\ TCConsistent)

THEOREM TPSpec => TCSpec
=============================================================================
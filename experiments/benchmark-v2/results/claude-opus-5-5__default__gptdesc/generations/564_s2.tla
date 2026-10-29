---------------------------- MODULE TwoPhase ----------------------------
(***************************************************************************)
(* Two-Phase Commit protocol.  A transaction manager (TM) coordinates a    *)
(* set RM of resource managers.  Messages are modeled as a set "msgs"      *)
(* that only grows; no messages are ever lost, and no faults are modeled.  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM   \* The set of resource managers

VARIABLES
  rmState,    \* rmState[r] is the state of resource manager r
  tmState,    \* The state of the transaction manager
  tmPrepared, \* The set of RMs from which the TM has received "Prepared"
  msgs        \* The set of all messages that have been sent

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages ==
  [type : {"Prepared"}, rm : RM] \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
(* Type invariant *)
TPTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

(* Safety: no RM commits while another aborts *)
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

(* Safety: the TM's decision is consistent with the RMs' states *)
TMConsistent ==
  /\ (tmState = "committed") => \A r \in RM : rmState[r] # "aborted"
  /\ (tmState = "aborted")   => \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------
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

-----------------------------------------------------------------------------
TPNext ==
  \/ TMCommit
  \/ TMAbort
  \/ \E r \in RM :
       \/ TMRcvPrepared(r)
       \/ RMPrepare(r)
       \/ RMChooseToAbort(r)
       \/ RMRcvCommitMsg(r)
       \/ RMRcvAbortMsg(r)

TPSpec == TPInit /\ [][TPNext]_vars

(* Standard aliases *)
Init == TPInit
Next == TPNext
Spec == TPSpec

-----------------------------------------------------------------------------
THEOREM TPSpec => [](TPTypeOK /\ TCConsistent /\ TMConsistent)
=============================================================================
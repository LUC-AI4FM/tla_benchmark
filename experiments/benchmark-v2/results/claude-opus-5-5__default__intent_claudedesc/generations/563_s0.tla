------------------------------- MODULE TwoPhase -------------------------------
EXTENDS TLC

CONSTANT RM

VARIABLES
  rmState,
  tmState,
  tmPrepared,
  msgs

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages ==
  [type : {"Prepared"}, rm : RM] \cup [type : {"Commit", "Abort"}]

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

-----------------------------------------------------------------------------
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

Init == TPInit
Next == TPNext
Spec == TPSpec

-----------------------------------------------------------------------------
(* Abstract Transaction Commit specification (TCommit), stated over rmState *)

TCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed"

Prepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) ==
  \/ /\ rmState[r] = "prepared"
     /\ canCommit
     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  \/ /\ rmState[r] \in {"working", "prepared"}
     /\ notCommitted
     /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

TCSpec == TCInit /\ [][TCNext]_rmState

(* Agreement: no RM has committed while another has aborted *)
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

(* Validity: a commit only happens if all RMs were willing to commit *)
TCValidity ==
  (\E r \in RM : rmState[r] = "committed")
     => \A r \in RM : rmState[r] \in {"prepared", "committed"}

(* Finality: once committed or aborted, an RM's decision never changes *)
DecisionFinal ==
  [][\A r \in RM :
       /\ (rmState[r] = "committed" => rmState'[r] = "committed")
       /\ (rmState[r] = "aborted"   => rmState'[r] = "aborted")]_vars

(* Additional protocol safety: RMs commit only if the TM decided commit *)
CommitOnlyIfTMCommitted ==
  (\E r \in RM : rmState[r] = "committed") => tmState = "committed"

TMCommitOnlyIfAllPrepared ==
  tmState = "committed" => tmPrepared = RM

-----------------------------------------------------------------------------

THEOREM TPSpec => [](TPTypeOK /\ TCConsistent)

(* Two-phase commit refines (implements) the Transaction Commit spec *)
THEOREM TPSpec => TCSpec

=============================================================================
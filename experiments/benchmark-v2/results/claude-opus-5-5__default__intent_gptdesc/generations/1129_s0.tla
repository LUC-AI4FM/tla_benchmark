---------------------------- MODULE TwoPhaseCommit ----------------------------
(***************************************************************************)
(* A model of the Two-Phase Commit protocol between one transaction        *)
(* manager (coordinator, TM) and a finite set of resource managers (RM).   *)
(* Messages are modeled as a set that only grows; a message is "received"  *)
(* when an action is enabled by its presence in the set.                   *)
(* Only safety properties are specified; no fairness or liveness is given. *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT RM            \* The finite set of resource managers

VARIABLES
  rmState,             \* rmState[r] is the state of resource manager r
  tmState,             \* The state of the coordinator
  tmPrepared,          \* Set of RMs from which the TM has received "Prepared"
  msgs                 \* Set of all messages that have been sent

vars == <<rmState, tmState, tmPrepared, msgs>>

RMStates == {"working", "prepared", "committed", "aborted"}
TMStates == {"init", "committed", "aborted"}

Messages ==
  [type : {"Prepared"}, rm : RM] \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type and state invariant                                                *)
(***************************************************************************)
TypeOK ==
  /\ rmState \in [RM -> RMStates]
  /\ tmState \in TMStates
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

-----------------------------------------------------------------------------
Init ==
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)

\* The TM receives a "Prepared" message from resource manager r.
TMRcvPrepared(r) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

\* The TM commits only after receiving "Prepared" from every RM,
\* and broadcasts the Commit decision.
TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

\* The TM may spontaneously abort at any time while undecided,
\* broadcasting the Abort decision.
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

(***************************************************************************)
(* Resource manager actions                                                *)
(***************************************************************************)

\* RM r prepares and sends a "Prepared" message to the TM.
RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>

\* RM r spontaneously decides to abort (only while still working).
RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* RM r receives the Commit decision.
RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* RM r receives the Abort decision.
RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

-----------------------------------------------------------------------------
Next ==
  \/ TMCommit
  \/ TMAbort
  \/ \E r \in RM :
       \/ TMRcvPrepared(r)
       \/ RMPrepare(r)
       \/ RMChooseToAbort(r)
       \/ RMRcvCommitMsg(r)
       \/ RMRcvAbortMsg(r)

\* Safety-only specification: no fairness, no liveness.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

\* Atomicity: no RM is committed while another is aborted.
Consistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

\* The TM only commits once every RM has indicated prepared.
TMCommitValid ==
  tmState = "committed" => tmPrepared = RM

\* If any RM has aborted, the TM must not have committed.
NoCommitIfAborted ==
  (\E r \in RM : rmState[r] = "aborted") => tmState # "committed"

\* A Commit message exists only if the TM has committed with all prepared.
CommitMsgValid ==
  [type |-> "Commit"] \in msgs => (tmState = "committed" /\ tmPrepared = RM)

\* Commit and Abort decisions are never both sent.
DecisionUnique ==
  ~ ([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)

\* Coordinator and participant decisions agree.
TMRMAgreement ==
  /\ tmState = "committed" =>
        \A r \in RM : rmState[r] \in {"prepared", "committed"}
  /\ \A r \in RM : rmState[r] = "committed" => tmState = "committed"

\* tmPrepared only contains RMs that actually sent Prepared.
PreparedValid ==
  \A r \in tmPrepared : [type |-> "Prepared", rm |-> r] \in msgs

Inv ==
  /\ TypeOK
  /\ Consistent
  /\ TMCommitValid
  /\ NoCommitIfAborted
  /\ CommitMsgValid
  /\ DecisionUnique
  /\ TMRMAgreement
  /\ PreparedValid

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties over transitions (action properties)                  *)
(***************************************************************************)

\* Coordinator decisions are stable.
TMStable ==
  [][ /\ (tmState = "committed" => tmState' = "committed")
      /\ (tmState = "aborted"   => tmState' = "aborted") ]_vars

\* Resource managers never leave committed or aborted states.
RMStable ==
  [][ \A r \in RM :
        /\ (rmState[r] = "committed" => rmState'[r] = "committed")
        /\ (rmState[r] = "aborted"   => rmState'[r] = "aborted") ]_vars

\* The coordinator transitions to committed only if all RMs prepared
\* and none has aborted.
TMCommitTransitionValid ==
  [][ (tmState # "committed" /\ tmState' = "committed") =>
        /\ tmPrepared = RM
        /\ \A r \in RM : rmState[r] # "aborted" ]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => TMStable /\ RMStable /\ TMCommitTransitionValid
=============================================================================
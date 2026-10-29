------------------------------ MODULE TwoPhaseCommit ------------------------------
(***************************************************************************)
(* A model of the two-phase commit protocol with one transaction manager   *)
(* (TM) and a set RM of resource managers.                                 *)
(*                                                                         *)
(* Messages are kept in a set "msgs". A message is never removed, so it    *)
(* may be delivered any number of times, in any order, and at any time.    *)
(* This gives asynchronous, unordered, duplicating delivery. It also       *)
(* gives eventual delivery of the TM's decision without assuming any       *)
(* reliable broadcast primitive.                                           *)
(*                                                                         *)
(* RM failures and recoveries are nondeterministic state changes. A failed *)
(* RM takes no protocol steps. Its protocol state is on stable storage, so *)
(* it survives the failure.                                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM            \* The set of resource managers

VARIABLES
  rmState,      \* rmState[rm] : lifecycle state of resource manager rm
  tmState,      \* "init", "committed" or "aborted"
  tmAsked,      \* RMs the TM has asked to prepare
  tmPrepared,   \* RMs the TM knows to be prepared
  msgs,         \* set of all messages sent so far
  failed        \* set of currently failed RMs

vars == <<rmState, tmState, tmAsked, tmPrepared, msgs, failed>>

Messages ==
       [type : {"Prepare", "Prepared"}, rm : RM]
  \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmAsked \subseteq RM
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages
  /\ failed \subseteq RM

Init ==
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmAsked = {}
  /\ tmPrepared = {}
  /\ msgs = {}
  /\ failed = {}

-----------------------------------------------------------------------------
(* Transaction manager actions *)

TMSendPrepare(rm) ==
  /\ tmState = "init"
  /\ rm \notin tmAsked
  /\ tmAsked' = tmAsked \cup {rm}
  /\ msgs' = msgs \cup {[type |-> "Prepare", rm |-> rm]}
  /\ UNCHANGED <<rmState, tmState, tmPrepared, failed>>

TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ rm \in tmAsked
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, tmAsked, msgs, failed>>

(* Commit only if every RM was asked to prepare and every RM that was      *)
(* asked has responded "Prepared".                                         *)
TMCommit ==
  /\ tmState = "init"
  /\ tmAsked = RM
  /\ tmPrepared = tmAsked
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmAsked, tmPrepared, failed>>

(* The TM may decide to abort at any time before it decides. When it      *)
(* aborts, it discards its knowledge of prepared RMs.                      *)
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ tmPrepared' = {}
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmAsked, failed>>

-----------------------------------------------------------------------------
(* Resource manager actions. A failed RM takes no protocol steps. *)

RMRcvPrepare(rm) ==
  /\ rm \notin failed
  /\ rmState[rm] = "working"
  /\ [type |-> "Prepare", rm |-> rm] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmAsked, tmPrepared, failed>>

(* A working RM may unilaterally abort. *)
RMChooseToAbort(rm) ==
  /\ rm \notin failed
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmAsked, tmPrepared, msgs, failed>>

RMRcvCommitMsg(rm) ==
  /\ rm \notin failed
  /\ rmState[rm] = "prepared"
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmAsked, tmPrepared, msgs, failed>>

RMRcvAbortMsg(rm) ==
  /\ rm \notin failed
  /\ rmState[rm] \in {"working", "prepared"}
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmAsked, tmPrepared, msgs, failed>>

(* Failures and recoveries are nondeterministic state changes. *)
RMFail(rm) ==
  /\ rm \notin failed
  /\ failed' = failed \cup {rm}
  /\ UNCHANGED <<rmState, tmState, tmAsked, tmPrepared, msgs>>

RMRecover(rm) ==
  /\ rm \in failed
  /\ failed' = failed \ {rm}
  /\ UNCHANGED <<rmState, tmState, tmAsked, tmPrepared, msgs>>

-----------------------------------------------------------------------------
Next ==
  \/ TMCommit
  \/ TMAbort
  \/ \E rm \in RM :
       \/ TMSendPrepare(rm)
       \/ TMRcvPrepared(rm)
       \/ RMRcvPrepare(rm)
       \/ RMChooseToAbort(rm)
       \/ RMRcvCommitMsg(rm)
       \/ RMRcvAbortMsg(rm)
       \/ RMFail(rm)
       \/ RMRecover(rm)

(***************************************************************************)
(* Fairness: messages are delivered and processed fairly.                  *)
(*  - The TM's steps get weak fairness.                                    *)
(*  - RM message-processing steps get strong fairness. An RM may fail and  *)
(*    recover repeatedly, so these steps are only enabled intermittently.  *)
(* Unilateral aborts, failures and recoveries get no fairness.             *)
(***************************************************************************)
Fairness ==
  /\ WF_vars(TMCommit)
  /\ WF_vars(TMAbort)
  /\ \A rm \in RM :
       /\ WF_vars(TMSendPrepare(rm))
       /\ WF_vars(TMRcvPrepared(rm))
       /\ SF_vars(RMRcvPrepare(rm))
       /\ SF_vars(RMRcvCommitMsg(rm))
       /\ SF_vars(RMRcvAbortMsg(rm))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* No RM commits unless the TM has decided to commit. *)
CommitOnlyIfTMCommitted ==
  \A rm \in RM : rmState[rm] = "committed" => tmState = "committed"

(* No conflicting terminal states. *)
NoConflictingTerminalStates ==
  ~ \E r1, r2 \in RM : rmState[r1] = "committed" /\ rmState[r2] = "aborted"

(* No RM is both committed and aborted. *)
NoRMBothCommittedAndAborted ==
  \A rm \in RM : ~(rmState[rm] = "committed" /\ rmState[rm] = "aborted")

(* The TM never believes an aborted RM is prepared. *)
PreparedNeverAborted ==
  \A rm \in tmPrepared : rmState[rm] # "aborted"

(* The TM's decision agrees with the RMs' terminal states. *)
DecisionConsistent ==
  /\ tmState = "aborted" => \A rm \in RM : rmState[rm] # "committed"
  /\ tmState = "committed" => \A rm \in RM : rmState[rm] # "aborted"

Safety ==
  /\ TypeOK
  /\ CommitOnlyIfTMCommitted
  /\ NoConflictingTerminalStates
  /\ NoRMBothCommittedAndAborted
  /\ PreparedNeverAborted
  /\ DecisionConsistent

THEOREM Spec => []Safety

-----------------------------------------------------------------------------
(* Liveness properties, under the fairness assumptions above *)

(* A global decision is eventually made. *)
EventuallyDecided == <>(tmState \in {"committed", "aborted"})

(* Each RM that is not failed eventually reaches the TM's decision. *)
CommitPropagates ==
  \A rm \in RM :
    (tmState = "committed") ~> (rmState[rm] = "committed" \/ rm \in failed)

AbortPropagates ==
  \A rm \in RM :
    (tmState = "aborted") ~> (rmState[rm] = "aborted" \/ rm \in failed)

(* Once a decision exists, an RM that stops failing reaches it for good. *)
DecisionReached ==
  \A rm \in RM :
    <>[](rm \notin failed) =>
      <>[](  (tmState = "committed" /\ rmState[rm] = "committed")
          \/ (tmState = "aborted"   /\ rmState[rm] = "aborted"))

Liveness ==
  /\ EventuallyDecided
  /\ CommitPropagates
  /\ AbortPropagates
  /\ DecisionReached

THEOREM Spec => Liveness
=============================================================================
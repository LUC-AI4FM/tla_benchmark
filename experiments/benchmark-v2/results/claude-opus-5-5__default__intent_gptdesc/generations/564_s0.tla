------------------------------- MODULE TwoPhaseCommit -------------------------------
(***************************************************************************)
(* A model of the classic two-phase commit protocol with one coordinator   *)
(* (transaction manager, TM) and a fixed set of participants (resource     *)
(* managers, RMs). Messages are asynchronous and unordered. Every message  *)
(* ever sent stays in the set msgs, so a message can be received any       *)
(* number of times, in any order.                                          *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT RM   \* The fixed set of participants (resource managers)

VARIABLES
  rmState,     \* rmState[r] is the state of participant r
  tmState,     \* The state of the coordinator: "init", "committed" or "aborted"
  tmPrepared,  \* The set of RMs from which the TM has received "Prepared"
  msgs         \* The set of all messages that have been sent

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages ==
  [type : {"Prepared"}, rm : RM] \cup [type : {"Commit", "Abort"}]

TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

Init ==
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

---------------------------------------------------------------------------
(* Coordinator (TM) actions *)

\* The TM receives a "Prepared" message from participant r.
TMRcvPrepared(r) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

\* The TM commits only after it has received "Prepared" from every participant.
TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

\* The TM may abort at any time before it has decided.
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

---------------------------------------------------------------------------
(* Participant (RM) actions *)

\* Participant r prepares and sends "Prepared" to the TM.
RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>

\* Participant r decides on its own to abort before it has prepared.
RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* Participant r receives the global "Commit" message.
RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

\* Participant r receives the global "Abort" message.
RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

---------------------------------------------------------------------------
Next ==
  \/ TMCommit
  \/ TMAbort
  \/ \E r \in RM :
       \/ TMRcvPrepared(r)
       \/ RMPrepare(r)
       \/ RMChooseToAbort(r)
       \/ RMRcvCommitMsg(r)
       \/ RMRcvAbortMsg(r)

\* Fairness: the coordinator does not wait forever without deciding, and
\* messages that have been sent are eventually received. The model does not
\* prescribe any other scheduling.
Fairness ==
  /\ WF_vars(TMCommit)
  /\ WF_vars(TMAbort)
  /\ \A r \in RM :
       /\ WF_vars(TMRcvPrepared(r))
       /\ WF_vars(RMRcvCommitMsg(r))
       /\ WF_vars(RMRcvAbortMsg(r))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

\* Agreement: no participant is committed while another is aborted.
Agreement ==
  \A r1, r2 \in RM :
    ~ (rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* Validity: a participant can be committed only if every participant
\* has indicated that it is ready, which the coordinator has recorded.
Validity ==
  (\E r \in RM : rmState[r] = "committed") =>
     /\ tmPrepared = RM
     /\ \A r \in RM : [type |-> "Prepared", rm |-> r] \in msgs

\* The coordinator's decision matches the Prepared messages it collected.
CoordinatorConsistency ==
  /\ (tmState = "committed") => (tmPrepared = RM)
  /\ ([type |-> "Commit"] \in msgs) => (tmPrepared = RM)
  /\ \A r \in tmPrepared : [type |-> "Prepared", rm |-> r] \in msgs

\* Commit and Abort are never both sent.
NoConflictingDecisions ==
  ~ ([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)

Inv ==
  /\ TypeOK
  /\ Agreement
  /\ Validity
  /\ CoordinatorConsistency
  /\ NoConflictingDecisions

---------------------------------------------------------------------------
(* Liveness properties *)

\* The coordinator eventually issues either Commit or Abort.
EventualDecision == <>(tmState \in {"committed", "aborted"})

\* Every participant eventually reaches a terminal state.
EventualTermination ==
  <>(\A r \in RM : rmState[r] \in {"committed", "aborted"})

\* Once the coordinator decides, all participants eventually follow that decision.
DecisionPropagates ==
  /\ (tmState = "committed") ~> (\A r \in RM : rmState[r] = "committed")
  /\ (tmState = "aborted")   ~> (\A r \in RM : rmState[r] = "aborted")

---------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => EventualDecision /\ EventualTermination /\ DecisionPropagates
=====================================================================================
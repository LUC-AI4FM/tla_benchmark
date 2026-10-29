------------------------------- MODULE TwoPhase -------------------------------
(***************************************************************************)
(* The classic two-phase commit protocol: one transaction manager (TM)     *)
(* and a set RM of resource managers. Messages are asynchronous and        *)
(* unordered. The variable msgs holds every message that has been sent,    *)
(* and messages are never removed.                                         *)
(***************************************************************************)
CONSTANT RM   \* The set of resource managers (participants)

VARIABLES
  rmState,     \* rmState[r] is the state of resource manager r
  tmState,     \* The state of the transaction manager
  tmPrepared,  \* The set of RMs from which the TM has received "Prepared"
  msgs         \* The set of all messages that have been sent

vars == <<rmState, tmState, tmPrepared, msgs>>

Messages ==
  (*************************************************************************)
  (* The set of all possible messages.                                     *)
  (*************************************************************************)
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

(* Optional liveness: fair scheduling of the TM's and RMs' actions. *)
TPFairSpec ==
  /\ TPSpec
  /\ WF_vars(TMCommit)
  /\ WF_vars(TMAbort)
  /\ \A r \in RM : /\ WF_vars(TMRcvPrepared(r))
                   /\ WF_vars(RMRcvCommitMsg(r))
                   /\ WF_vars(RMRcvAbortMsg(r))

-----------------------------------------------------------------------------
(* Safety properties *)

\* Agreement: no RM is committed while another is aborted.
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

\* The coordinator commits only after receiving Prepared from every RM.
TMConsistent ==
  /\ (tmState = "committed") => (tmPrepared = RM)
  /\ ([type |-> "Commit"] \in msgs) => (tmPrepared = RM)
  /\ \A r \in tmPrepared : [type |-> "Prepared", rm |-> r] \in msgs

\* Validity: an RM is committed only if every RM had indicated readiness.
Validity ==
  (\E r \in RM : rmState[r] = "committed") =>
     \A r \in RM : [type |-> "Prepared", rm |-> r] \in msgs

TPInvariant == TPTypeOK /\ TCConsistent /\ TMConsistent /\ Validity

(* Liveness: eventually the TM decides and all RMs reach a terminal state. *)
EventualDecision == <>(tmState \in {"committed", "aborted"})
EventualTermination == <>(\A r \in RM : rmState[r] \in {"committed", "aborted"})

THEOREM TPSpec => [](TPTypeOK /\ TCConsistent /\ TMConsistent /\ Validity)
=============================================================================
------------------------------- MODULE TwoPhase -------------------------------
(***************************************************************************)
(* A model of the Two-Phase Commit protocol between one transaction       *)
(* manager (coordinator) and a set RM of resource managers.  Messages are *)
(* never removed from the set msgs, so receiving a message is modeled by  *)
(* the message being present in msgs.                                      *)
(***************************************************************************)
CONSTANT RM

VARIABLES
  rmState,     \* rmState[r] is the state of resource manager r
  tmState,     \* the state of the coordinator
  tmPrepared,  \* the set of RMs from which the coordinator received "Prepared"
  msgs         \* the set of all messages that have been sent

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
(* Coordinator actions *)

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
  \/ TMCommit
  \/ TMAbort
  \/ \E r \in RM :
       \/ TMRcvPrepared(r)
       \/ RMPrepare(r)
       \/ RMChooseToAbort(r)
       \/ RMRcvCommitMsg(r)
       \/ RMRcvAbortMsg(r)

TPSpec == TPInit /\ [][TPNext]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

\* Atomicity: no RM committed while another RM aborted.
TPConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

\* Coordinator may only have committed if every RM was prepared.
TMCommitValid ==
  (tmState = "committed") => (tmPrepared = RM)

\* Coordinator commit is incompatible with any RM having aborted.
TMCommitNoAbortedRM ==
  (tmState = "committed") => \A r \in RM : rmState[r] # "aborted"

\* Commit and Abort messages are never both sent.
TPMsgsConsistent ==
  ~ ( [type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs )

TPInvariant ==
  /\ TPTypeOK
  /\ TPConsistent
  /\ TMCommitValid
  /\ TMCommitNoAbortedRM
  /\ TPMsgsConsistent

(* Stability (action) properties *)

TMDecisionStable ==
  /\ [][tmState = "committed" => tmState' = "committed"]_vars
  /\ [][tmState = "aborted" => tmState' = "aborted"]_vars

RMDecisionStable ==
  \A r \in RM :
    /\ [][rmState[r] = "committed" => rmState'[r] = "committed"]_vars
    /\ [][rmState[r] = "aborted" => rmState'[r] = "aborted"]_vars

THEOREM TPSpec => []TPInvariant
=============================================================================
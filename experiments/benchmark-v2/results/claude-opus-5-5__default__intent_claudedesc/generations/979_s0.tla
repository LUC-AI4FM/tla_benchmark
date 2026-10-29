--------------------------- MODULE TwoPhaseProtocol ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    RM,            \* the set of participant processes
    VoteOptions    \* the votes a participant may cast, e.g. {"yes","no"}

ASSUME RM # {}
ASSUME VoteOptions \subseteq {"yes", "no"} /\ VoteOptions # {}

VARIABLES
    rmState,      \* rmState[r]: state of participant r
    rmVote,       \* rmVote[r]: the vote cast by participant r
    tmState,      \* state of the coordinator
    tmPrepared,   \* participants from which the coordinator received a "yes" vote
    voteMsgs,     \* phase 1 messages: votes sent from participants to the coordinator
    decisionMsg   \* phase 2 message: decision broadcast by the coordinator

vars == <<rmState, rmVote, tmState, tmPrepared, voteMsgs, decisionMsg>>

RMStates    == {"working", "prepared", "committed", "aborted"}
TMStates    == {"init", "committed", "aborted"}
Votes       == {"none", "yes", "no"}
VoteMessage == [rm : RM, vote : {"yes", "no"}]
Decisions   == {"none", "commit", "abort"}

-----------------------------------------------------------------------------
TypeOK ==
    /\ rmState \in [RM -> RMStates]
    /\ rmVote \in [RM -> Votes]
    /\ tmState \in TMStates
    /\ tmPrepared \subseteq RM
    /\ voteMsgs \subseteq VoteMessage
    /\ decisionMsg \in Decisions

Init ==
    /\ rmState = [r \in RM |-> "working"]
    /\ rmVote = [r \in RM |-> "none"]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ voteMsgs = {}
    /\ decisionMsg = "none"

-----------------------------------------------------------------------------
(* Phase 1: participants vote; the coordinator collects votes. *)

RMVoteYes(r) ==
    /\ "yes" \in VoteOptions
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ rmVote' = [rmVote EXCEPT ![r] = "yes"]
    /\ voteMsgs' = voteMsgs \cup {[rm |-> r, vote |-> "yes"]}
    /\ UNCHANGED <<tmState, tmPrepared, decisionMsg>>

RMVoteNo(r) ==
    /\ "no" \in VoteOptions
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ rmVote' = [rmVote EXCEPT ![r] = "no"]
    /\ voteMsgs' = voteMsgs \cup {[rm |-> r, vote |-> "no"]}
    /\ UNCHANGED <<tmState, tmPrepared, decisionMsg>>

RMVote(r) == RMVoteYes(r) \/ RMVoteNo(r)

TMRcvPrepared(r) ==
    /\ tmState = "init"
    /\ [rm |-> r, vote |-> "yes"] \in voteMsgs
    /\ r \notin tmPrepared
    /\ tmPrepared' = tmPrepared \cup {r}
    /\ UNCHANGED <<rmState, rmVote, tmState, voteMsgs, decisionMsg>>

(* Phase 2: the coordinator decides and broadcasts; participants apply it. *)

TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ decisionMsg' = "commit"
    /\ UNCHANGED <<rmState, rmVote, tmPrepared, voteMsgs>>

TMAbort ==
    /\ tmState = "init"
    /\ \E r \in RM : [rm |-> r, vote |-> "no"] \in voteMsgs
    /\ tmState' = "aborted"
    /\ decisionMsg' = "abort"
    /\ UNCHANGED <<rmState, rmVote, tmPrepared, voteMsgs>>

RMRcvCommit(r) ==
    /\ rmState[r] = "prepared"
    /\ decisionMsg = "commit"
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<rmVote, tmState, tmPrepared, voteMsgs, decisionMsg>>

RMRcvAbort(r) ==
    /\ rmState[r] = "prepared"
    /\ decisionMsg = "abort"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<rmVote, tmState, tmPrepared, voteMsgs, decisionMsg>>

RMRcvDecision(r) == RMRcvCommit(r) \/ RMRcvAbort(r)

(* Terminal stuttering, to avoid reporting deadlock once the protocol ends. *)
Terminated ==
    /\ tmState # "init"
    /\ \A r \in RM : rmState[r] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ TMCommit
    \/ TMAbort
    \/ \E r \in RM : RMVote(r) \/ TMRcvPrepared(r) \/ RMRcvDecision(r)
    \/ Terminated

Fairness ==
    /\ WF_vars(TMCommit)
    /\ WF_vars(TMAbort)
    /\ \A r \in RM : WF_vars(RMVote(r))
    /\ \A r \in RM : WF_vars(TMRcvPrepared(r))
    /\ \A r \in RM : WF_vars(RMRcvDecision(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Agreement: no two participants reach different final decisions.
Agreement ==
    \A r1, r2 \in RM :
        ~(rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* Participant outcomes are consistent with the coordinator's decision.
ConsistentWithCoordinator ==
    \A r \in RM :
        /\ rmState[r] = "committed" => tmState = "committed"
        /\ (rmState[r] = "aborted" /\ rmVote[r] = "yes") => tmState = "aborted"

\* Validity: commit only if all voted yes; abort only if someone voted no.
Validity ==
    /\ (tmState = "committed") => \A r \in RM : rmVote[r] = "yes"
    /\ (tmState = "aborted")   => \E r \in RM : rmVote[r] = "no"
    /\ (\E r \in RM : rmState[r] = "committed") => \A r \in RM : rmVote[r] = "yes"

\* The coordinator's decision is broadcast faithfully.
DecisionConsistency ==
    /\ (decisionMsg = "commit") <=> (tmState = "committed")
    /\ (decisionMsg = "abort")  <=> (tmState = "aborted")

Safety == TypeOK /\ Agreement /\ ConsistentWithCoordinator
          /\ Validity /\ DecisionConsistency

THEOREM Spec => []Safety

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Termination: the coordinator decides and every participant finishes.
Termination ==
    <>( /\ tmState # "init"
        /\ \A r \in RM : rmState[r] \in {"committed", "aborted"} )

\* Once a decision is made, it is never revoked.
DecisionStable ==
    /\ [](tmState = "committed" => [](tmState = "committed"))
    /\ [](tmState = "aborted"   => [](tmState = "aborted"))

\* If every participant votes yes, the protocol eventually commits.
CommitIfAllYes ==
    (\A r \in RM : rmVote[r] = "yes") ~> (\A r \in RM : rmState[r] = "committed")

THEOREM Spec => Termination /\ DecisionStable /\ CommitIfAllYes
=============================================================================
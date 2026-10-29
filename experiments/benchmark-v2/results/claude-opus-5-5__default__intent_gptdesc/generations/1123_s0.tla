---------------------------- MODULE TwoPhaseCommitFT ----------------------------
(***************************************************************************)
(* Two-phase commit for a single transaction, with one coordinator (TM)   *)
(* and a finite set of resource managers (RMs).                           *)
(*                                                                         *)
(* Network: messages live in a set `msgs`.  Delivery does not consume a    *)
(* message, so a message can be delayed or delivered more than once.       *)
(* Messages may be lost (LoseMsg) but are never corrupted.                 *)
(*                                                                         *)
(* Crashes: the coordinator and any RM may crash and later recover.        *)
(* rmState, rmVote and tmState model stable (persisted) storage and        *)
(* survive crashes.  The coordinator's set of collected yes-votes          *)
(* (tmPrepared) is volatile and is lost on a crash.  A coordinator that    *)
(* recovers without a persisted decision uses presumed abort.              *)
(*                                                                         *)
(* Timeouts are modelled as actions that are always allowed to fire in     *)
(* the right state.  They lead to abort decisions, resent prepare          *)
(* requests, resent votes (status queries) or resent decisions.            *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT RM            \* the finite set of participating resource managers

ASSUME RM # {} /\ IsFiniteSet(RM)

VARIABLES
  rmState,     \* persisted: RM -> {"working","prepared","committed","aborted"}
  rmVote,      \* persisted: RM -> {"none","yes","no"}
  rmUp,        \* RM -> BOOLEAN   (FALSE = crashed)
  tmState,     \* persisted: {"init","waiting","committed","aborted"}
  tmPrepared,  \* volatile: set of RMs from which a yes-vote was received
  tmUp,        \* BOOLEAN         (FALSE = coordinator crashed)
  msgs         \* set of in-flight messages

vars == <<rmState, rmVote, rmUp, tmState, tmPrepared, tmUp, msgs>>

RMStates  == {"working", "prepared", "committed", "aborted"}
Decided   == {"committed", "aborted"}
TMStates  == {"init", "waiting", "committed", "aborted"}

Messages ==
       [type : {"prepare", "commit", "abort"}]
  \cup [type : {"vote"}, rm : RM, vote : {"yes", "no"}]

PrepareMsg == [type |-> "prepare"]
CommitMsg  == [type |-> "commit"]
AbortMsg   == [type |-> "abort"]
VoteMsg(r, v) == [type |-> "vote", rm |-> r, vote |-> v]

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
TypeOK ==
  /\ rmState \in [RM -> RMStates]
  /\ rmVote \in [RM -> {"none", "yes", "no"}]
  /\ rmUp \in [RM -> BOOLEAN]
  /\ tmState \in TMStates
  /\ tmPrepared \subseteq RM
  /\ tmUp \in BOOLEAN
  /\ msgs \subseteq Messages

Init ==
  /\ rmState = [r \in RM |-> "working"]
  /\ rmVote = [r \in RM |-> "none"]
  /\ rmUp = [r \in RM |-> TRUE]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ tmUp = TRUE
  /\ msgs = {}

-----------------------------------------------------------------------------
(*************************** Coordinator actions ***************************)

\* Phase 1: start the protocol by asking all RMs to prepare.
TMSendPrepare ==
  /\ tmUp
  /\ tmState = "init"
  /\ tmState' = "waiting"
  /\ Send(PrepareMsg)
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmPrepared, tmUp>>

\* Timeout: resend a prepare request that may have been lost.
TMResendPrepare ==
  /\ tmUp
  /\ tmState = "waiting"
  /\ PrepareMsg \notin msgs
  /\ Send(PrepareMsg)
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmState, tmPrepared, tmUp>>

\* Receive a yes-vote.
TMRcvYes(r) ==
  /\ tmUp
  /\ tmState = "waiting"
  /\ VoteMsg(r, "yes") \in msgs
  /\ r \notin tmPrepared
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmState, tmUp, msgs>>

\* Receive a no-vote: the coordinator must abort.
TMRcvNo(r) ==
  /\ tmUp
  /\ tmState = "waiting"
  /\ VoteMsg(r, "no") \in msgs
  /\ tmState' = "aborted"
  /\ Send(AbortMsg)
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmPrepared, tmUp>>

\* Phase 2: commit only if every RM has prepared (voted yes).
TMCommit ==
  /\ tmUp
  /\ tmState = "waiting"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ Send(CommitMsg)
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmPrepared, tmUp>>

\* Timeout (or unilateral choice) before a commit decision: abort.
TMTimeoutAbort ==
  /\ tmUp
  /\ tmState \in {"init", "waiting"}
  /\ tmState' = "aborted"
  /\ Send(AbortMsg)
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmPrepared, tmUp>>

\* Timeout or query: resend the persisted decision.
TMResendDecision ==
  /\ tmUp
  /\ \/ tmState = "committed" /\ CommitMsg \notin msgs /\ Send(CommitMsg)
     \/ tmState = "aborted"   /\ AbortMsg  \notin msgs /\ Send(AbortMsg)
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmState, tmPrepared, tmUp>>

\* Coordinator crash: volatile state (collected votes) is lost.
TMCrash ==
  /\ tmUp
  /\ tmUp' = FALSE
  /\ tmPrepared' = {}
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmState, msgs>>

\* Coordinator recovery from stable storage.  An undecided
\* transaction is aborted (presumed abort).
TMRecover ==
  /\ ~tmUp
  /\ tmUp' = TRUE
  /\ IF tmState \in {"init", "waiting"}
       THEN /\ tmState' = "aborted"
            /\ Send(AbortMsg)
       ELSE UNCHANGED <<tmState, msgs>>
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmPrepared>>

-----------------------------------------------------------------------------
(************************* Resource manager actions ************************)

\* Receive prepare and vote yes: persist "prepared" and send the vote.
RMVoteYes(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "working"
  /\ PrepareMsg \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ rmVote' = [rmVote EXCEPT ![r] = "yes"]
  /\ Send(VoteMsg(r, "yes"))
  /\ UNCHANGED <<rmUp, tmState, tmPrepared, tmUp>>

\* Receive prepare and vote no: abort locally and send the vote.
RMVoteNo(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "working"
  /\ PrepareMsg \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ rmVote' = [rmVote EXCEPT ![r] = "no"]
  /\ Send(VoteMsg(r, "no"))
  /\ UNCHANGED <<rmUp, tmState, tmPrepared, tmUp>>

RMRcvPrepare(r) == RMVoteYes(r) \/ RMVoteNo(r)

\* Timeout while working (no prepare received): unilateral abort.
RMTimeoutAbort(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ rmVote' = [rmVote EXCEPT ![r] = "no"]
  /\ Send(VoteMsg(r, "no"))
  /\ UNCHANGED <<rmUp, tmState, tmPrepared, tmUp>>

\* Timeout while prepared (in doubt): resend the vote, which also acts as
\* a status query.  A prepared RM may NOT decide unilaterally.
RMResendVote(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "prepared"
  /\ VoteMsg(r, "yes") \notin msgs
  /\ Send(VoteMsg(r, "yes"))
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmState, tmPrepared, tmUp>>

RMRcvCommit(r) ==
  /\ rmUp[r]
  /\ rmState[r] = "prepared"
  /\ CommitMsg \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<rmVote, rmUp, tmState, tmPrepared, tmUp, msgs>>

RMRcvAbort(r) ==
  /\ rmUp[r]
  /\ rmState[r] \in {"working", "prepared"}
  /\ AbortMsg \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<rmVote, rmUp, tmState, tmPrepared, tmUp, msgs>>

RMCrash(r) ==
  /\ rmUp[r]
  /\ rmUp' = [rmUp EXCEPT ![r] = FALSE]
  /\ UNCHANGED <<rmState, rmVote, tmState, tmPrepared, tmUp, msgs>>

\* Recovery from the persisted state.  An RM that never prepared aborts.
\* A prepared RM stays in doubt and re-sends its vote to learn the outcome.
\* A decided RM keeps its decision.
RMRecover(r) ==
  /\ ~rmUp[r]
  /\ rmUp' = [rmUp EXCEPT ![r] = TRUE]
  /\ CASE rmState[r] = "working" ->
            /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
            /\ rmVote' = [rmVote EXCEPT ![r] = "no"]
            /\ Send(VoteMsg(r, "no"))
       [] rmState[r] = "prepared" ->
            /\ Send(VoteMsg(r, "yes"))
            /\ UNCHANGED <<rmState, rmVote>>
       [] OTHER ->
            UNCHANGED <<rmState, rmVote, msgs>>
  /\ UNCHANGED <<tmState, tmPrepared, tmUp>>

-----------------------------------------------------------------------------
(****************************** Network faults *****************************)

LoseMsg(m) ==
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<rmState, rmVote, rmUp, tmState, tmPrepared, tmUp>>

-----------------------------------------------------------------------------
TMNext ==
  \/ TMSendPrepare \/ TMResendPrepare \/ TMCommit \/ TMTimeoutAbort
  \/ TMResendDecision \/ TMCrash \/ TMRecover
  \/ \E r \in RM : TMRcvYes(r) \/ TMRcvNo(r)

RMNext ==
  \E r \in RM :
    \/ RMRcvPrepare(r) \/ RMTimeoutAbort(r) \/ RMResendVote(r)
    \/ RMRcvCommit(r) \/ RMRcvAbort(r) \/ RMCrash(r) \/ RMRecover(r)

FaultStep ==
  \/ \E m \in msgs : LoseMsg(m)
  \/ \E r \in RM : RMCrash(r)
  \/ TMCrash

Next ==
  \/ TMNext
  \/ RMNext
  \/ \E m \in msgs : LoseMsg(m)

\* Safety-only specification (arbitrary asynchrony, loss and crashes).
Spec == Init /\ [][Next]_vars

\* Environment assumption: message loss and crashes eventually stop.
\* After that point, messages are eventually delivered and every crashed
\* party eventually recovers.
EnvEventuallyStable == <>[][~FaultStep]_vars

Fairness ==
  /\ WF_vars(TMSendPrepare)
  /\ WF_vars(TMResendPrepare)
  /\ WF_vars(TMCommit)
  /\ WF_vars(TMTimeoutAbort)
  /\ WF_vars(TMResendDecision)
  /\ WF_vars(TMRecover)
  /\ \A r \in RM :
       /\ WF_vars(TMRcvYes(r))
       /\ WF_vars(TMRcvNo(r))
       /\ WF_vars(RMRcvPrepare(r))
       /\ WF_vars(RMTimeoutAbort(r))
       /\ WF_vars(RMResendVote(r))
       /\ WF_vars(RMRcvCommit(r))
       /\ WF_vars(RMRcvAbort(r))
       /\ WF_vars(RMRecover(r))

FairSpec == Spec /\ Fairness /\ EnvEventuallyStable

-----------------------------------------------------------------------------
(******************************** Invariants *******************************)

\* Safety: no two participants reach conflicting terminal decisions.
Consistency ==
  \A r1, r2 \in RM :
    ~(rmState[r1] = "committed" /\ rmState[r2] = "aborted")

\* The coordinator's persisted decision agrees with every participant.
TMConsistency ==
  /\ tmState = "committed" => \A r \in RM : rmState[r] # "aborted"
  /\ tmState = "aborted"   => \A r \in RM : rmState[r] # "committed"

\* Validity: commit only if every participant voted yes.  If any
\* participant voted no, the transaction is never committed.
Validity ==
  /\ (tmState = "committed" \/ \E r \in RM : rmState[r] = "committed")
        => \A r \in RM : rmVote[r] = "yes"
  /\ (\E r \in RM : rmVote[r] = "no")
        => /\ tmState # "committed"
           /\ \A r \in RM : rmState[r] # "committed"

\* Commit is decided only when all participants are prepared or committed.
CommitRequiresPrepared ==
  tmState = "committed" => \A r \in RM : rmState[r] \in {"prepared", "committed"}

\* Persisted decisions never change.  (Action property.)
StableDecisions ==
  /\ \A r \in RM :
       /\ [][rmState[r] = "committed" => rmState'[r] = "committed"]_vars
       /\ [][rmState[r] = "aborted"   => rmState'[r] = "aborted"]_vars
  /\ [][tmState = "committed" => tmState' = "committed"]_vars
  /\ [][tmState = "aborted"   => tmState' = "aborted"]_vars

Safety == TypeOK /\ Consistency /\ TMConsistency /\ Validity /\ CommitRequiresPrepared

-----------------------------------------------------------------------------
(**************************** Liveness properties **************************)

\* Termination: eventually every non-crashed participant has decided.
Termination ==
  <>(\A r \in RM : rmUp[r] => rmState[r] \in Decided)

\* Stronger: once faults stop, every participant is eventually up and decided,
\* and stays so.
FullTermination ==
  <>[](\A r \in RM : rmUp[r] /\ rmState[r] \in Decided)

\* Agreement: all non-faulty participants eventually decide the same outcome.
Agreement ==
  \/ <>[](\A r \in RM : rmUp[r] => rmState[r] = "committed")
  \/ <>[](\A r \in RM : rmUp[r] => rmState[r] = "aborted")

\* The coordinator eventually reaches a decision.
TMDecides == <>(tmState \in Decided)

THEOREM Spec => [](Safety)
THEOREM Spec => StableDecisions
THEOREM FairSpec => Termination /\ FullTermination /\ Agreement /\ TMDecides
=============================================================================
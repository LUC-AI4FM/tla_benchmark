------------------------------- MODULE TwoPhaseCommitFT -------------------------------
(***************************************************************************)
(* Two-phase commit with a single coordinator and a fixed set of          *)
(* participants.                                                           *)
(*                                                                         *)
(*  - Asynchronous, unreliable channels.  Messages live in a set; they     *)
(*    may be delayed arbitrarily, reordered, duplicated (by resending) or  *)
(*    lost.  Every message is addressed to or from a specific participant, *)
(*    which gives per-recipient channels.                                  *)
(*  - Crash/recovery, non-Byzantine faults.  Logged (stable) state         *)
(*    survives a crash.  Volatile state is lost on a crash.                *)
(*  - Phase 1: the coordinator sends PREPARE.  Each participant's vote is  *)
(*    "none" (undecided), "yes" or "no".                                   *)
(*  - Phase 2: the coordinator logs the global decision.  It then sends    *)
(*    the decision to every participant.  Each participant first          *)
(*    receives the decision (volatile) and then applies it (stable).       *)
(*  - The number of crashes and message losses is bounded.  This models    *)
(*    the assumption that faults eventually stop, which liveness needs.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Participants,   \* finite set of participant identifiers
    MaxCrashes,     \* bound on the total number of crash events
    MaxLosses       \* bound on the total number of message losses

ASSUME /\ Participants # {}
       /\ IsFiniteSet(Participants)
       /\ MaxCrashes \in Nat
       /\ MaxLosses \in Nat

VARIABLES
    pState,     \* stable: [P -> {"working","prepared","committed","aborted"}]
    pVote,      \* stable: [P -> {"none","yes","no"}]  ("none" = undecided)
    pRecvDec,   \* volatile: decision received but not yet applied
    pUp,        \* [P -> BOOLEAN]  participant is running
    cState,     \* stable: {"init","waiting","committed","aborted"}
    cUp,        \* coordinator is running
    votesRecv,  \* coordinator's record of votes received (volatile while waiting)
    msgs,       \* the set of messages in transit
    crashCount, \* number of crashes so far
    lossCount   \* number of message losses so far

vars == << pState, pVote, pRecvDec, pUp, cState, cUp, votesRecv, msgs,
           crashCount, lossCount >>

-----------------------------------------------------------------------------
(* Messages *)

PrepareMsg(p)     == [type |-> "prepare",  dst |-> p]
VoteMsg(p, v)     == [type |-> "vote",     src |-> p, vote |-> v]
DecisionMsg(p, d) == [type |-> "decision", dst |-> p, dec |-> d]

Messages ==
         [type : {"prepare"},  dst : Participants]
    \cup [type : {"vote"},     src : Participants, vote : {"yes", "no"}]
    \cup [type : {"decision"}, dst : Participants, dec : {"commit", "abort"}]

Final == {"committed", "aborted"}

TypeOK ==
    /\ pState    \in [Participants -> {"working", "prepared", "committed", "aborted"}]
    /\ pVote     \in [Participants -> {"none", "yes", "no"}]
    /\ pRecvDec  \in [Participants -> {"none", "commit", "abort"}]
    /\ pUp       \in [Participants -> BOOLEAN]
    /\ cState    \in {"init", "waiting", "committed", "aborted"}
    /\ cUp       \in BOOLEAN
    /\ votesRecv \in [Participants -> {"none", "yes", "no"}]
    /\ msgs      \subseteq Messages
    /\ crashCount \in 0..MaxCrashes
    /\ lossCount  \in 0..MaxLosses

-----------------------------------------------------------------------------
Init ==
    /\ pState    = [p \in Participants |-> "working"]
    /\ pVote     = [p \in Participants |-> "none"]
    /\ pRecvDec  = [p \in Participants |-> "none"]
    /\ pUp       = [p \in Participants |-> TRUE]
    /\ cState    = "init"
    /\ cUp       = TRUE
    /\ votesRecv = [p \in Participants |-> "none"]
    /\ msgs      = {}
    /\ crashCount = 0
    /\ lossCount  = 0

-----------------------------------------------------------------------------
(* Coordinator actions *)

\* Phase 1: start the protocol and broadcast PREPARE.
CSendPrepare ==
    /\ cUp
    /\ cState = "init"
    /\ cState' = "waiting"
    /\ msgs' = msgs \cup {PrepareMsg(p) : p \in Participants}
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cUp, votesRecv,
                    crashCount, lossCount >>

\* Retransmit PREPARE to a participant whose vote is still missing.
CResendPrepare(p) ==
    /\ cUp
    /\ cState = "waiting"
    /\ votesRecv[p] = "none"
    /\ PrepareMsg(p) \notin msgs
    /\ msgs' = msgs \cup {PrepareMsg(p)}
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cState, cUp, votesRecv,
                    crashCount, lossCount >>

\* "Vote received" at the coordinator.
CReceiveVote(p) ==
    /\ cUp
    /\ cState = "waiting"
    /\ votesRecv[p] = "none"
    /\ \E v \in {"yes", "no"} :
          /\ VoteMsg(p, v) \in msgs
          /\ votesRecv' = [votesRecv EXCEPT ![p] = v]
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cState, cUp, msgs,
                    crashCount, lossCount >>

\* Phase 2: commit only if every vote received is yes.
\* The decision is logged first and then broadcast.
CCommit ==
    /\ cUp
    /\ cState = "waiting"
    /\ \A p \in Participants : votesRecv[p] = "yes"
    /\ cState' = "committed"
    /\ msgs' = msgs \cup {DecisionMsg(p, "commit") : p \in Participants}
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cUp, votesRecv,
                    crashCount, lossCount >>

\* Phase 2: abort if some vote received is no.
CAbort ==
    /\ cUp
    /\ cState = "waiting"
    /\ \E p \in Participants : votesRecv[p] = "no"
    /\ cState' = "aborted"
    /\ msgs' = msgs \cup {DecisionMsg(p, "abort") : p \in Participants}
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cUp, votesRecv,
                    crashCount, lossCount >>

\* Retransmit the logged decision to a participant (after a loss).
CResendDecision(p) ==
    /\ cUp
    /\ cState \in Final
    /\ LET d == IF cState = "committed" THEN "commit" ELSE "abort"
       IN  /\ DecisionMsg(p, d) \notin msgs
           /\ msgs' = msgs \cup {DecisionMsg(p, d)}
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cState, cUp, votesRecv,
                    crashCount, lossCount >>

\* Coordinator crash.  Votes collected but not yet acted on are volatile.
\* A logged decision and the votes that justified it are kept.
CCrash ==
    /\ cUp
    /\ crashCount < MaxCrashes
    /\ cUp' = FALSE
    /\ votesRecv' = IF cState = "waiting"
                       THEN [p \in Participants |-> "none"]
                       ELSE votesRecv
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cState, msgs, lossCount >>

\* Coordinator recovery.  It resumes from its stable log state.
CRecover ==
    /\ ~cUp
    /\ cUp' = TRUE
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cState, votesRecv, msgs,
                    crashCount, lossCount >>

-----------------------------------------------------------------------------
(* Participant actions *)

\* Receive PREPARE and cast a vote: "vote sent".
\* A yes vote moves the participant to prepared (in doubt).
\* A no vote lets it abort unilaterally.
PReceivePrepare(p) ==
    /\ pUp[p]
    /\ pState[p] = "working"
    /\ pVote[p] = "none"
    /\ PrepareMsg(p) \in msgs
    /\ \E v \in {"yes", "no"} :
          /\ pVote'  = [pVote EXCEPT ![p] = v]
          /\ pState' = [pState EXCEPT ![p] = IF v = "yes" THEN "prepared"
                                                          ELSE "aborted"]
          /\ msgs'   = msgs \cup {VoteMsg(p, v)}
    /\ UNCHANGED << pRecvDec, pUp, cState, cUp, votesRecv,
                    crashCount, lossCount >>

\* Unilateral abort before voting.  This counts as a "no" vote.
PUnilateralAbort(p) ==
    /\ pUp[p]
    /\ pState[p] = "working"
    /\ pVote[p] = "none"
    /\ pVote'  = [pVote EXCEPT ![p] = "no"]
    /\ pState' = [pState EXCEPT ![p] = "aborted"]
    /\ UNCHANGED << pRecvDec, pUp, cState, cUp, votesRecv, msgs,
                    crashCount, lossCount >>

\* Re-send the logged vote in reply to a PREPARE.
\* This covers a lost vote, or a vote forgotten by a crashed coordinator.
PResendVote(p) ==
    /\ pUp[p]
    /\ pVote[p] # "none"
    /\ PrepareMsg(p) \in msgs
    /\ VoteMsg(p, pVote[p]) \notin msgs
    /\ msgs' = msgs \cup {VoteMsg(p, pVote[p])}
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cState, cUp, votesRecv,
                    crashCount, lossCount >>

\* "Decision received" (held in volatile memory).
PReceiveDecision(p) ==
    /\ pUp[p]
    /\ pState[p] \in {"working", "prepared"}
    /\ pRecvDec[p] = "none"
    /\ \E d \in {"commit", "abort"} :
          /\ DecisionMsg(p, d) \in msgs
          /\ pRecvDec' = [pRecvDec EXCEPT ![p] = d]
    /\ UNCHANGED << pState, pVote, pUp, cState, cUp, votesRecv, msgs,
                    crashCount, lossCount >>

\* "Decision applied" (logged to stable storage).
PApplyDecision(p) ==
    /\ pUp[p]
    /\ pState[p] \in {"working", "prepared"}
    /\ pRecvDec[p] # "none"
    /\ pState' = [pState EXCEPT ![p] =
                     IF pRecvDec[p] = "commit" THEN "committed" ELSE "aborted"]
    /\ pRecvDec' = [pRecvDec EXCEPT ![p] = "none"]
    /\ UNCHANGED << pVote, pUp, cState, cUp, votesRecv, msgs,
                    crashCount, lossCount >>

\* Participant crash.  The volatile received-but-unapplied decision is lost.
PCrash(p) ==
    /\ pUp[p]
    /\ crashCount < MaxCrashes
    /\ pUp' = [pUp EXCEPT ![p] = FALSE]
    /\ pRecvDec' = [pRecvDec EXCEPT ![p] = "none"]
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED << pState, pVote, cState, cUp, votesRecv, msgs, lossCount >>

\* Participant recovery.  pState and pVote come back from stable storage.
PRecover(p) ==
    /\ ~pUp[p]
    /\ pUp' = [pUp EXCEPT ![p] = TRUE]
    /\ UNCHANGED << pState, pVote, pRecvDec, cState, cUp, votesRecv, msgs,
                    crashCount, lossCount >>

-----------------------------------------------------------------------------
(* Unreliable network *)

LoseMsg ==
    /\ lossCount < MaxLosses
    /\ \E m \in msgs : msgs' = msgs \ {m}
    /\ lossCount' = lossCount + 1
    /\ UNCHANGED << pState, pVote, pRecvDec, pUp, cState, cUp, votesRecv,
                    crashCount >>

-----------------------------------------------------------------------------
Next ==
    \/ CSendPrepare
    \/ CCommit
    \/ CAbort
    \/ CCrash
    \/ CRecover
    \/ LoseMsg
    \/ \E p \in Participants :
          \/ CResendPrepare(p)
          \/ CReceiveVote(p)
          \/ CResendDecision(p)
          \/ PReceivePrepare(p)
          \/ PUnilateralAbort(p)
          \/ PResendVote(p)
          \/ PReceiveDecision(p)
          \/ PApplyDecision(p)
          \/ PCrash(p)
          \/ PRecover(p)

(***************************************************************************)
(* Fairness.  Faults (crashes, losses) are bounded and never forced.      *)
(* Every protocol step, retransmission and recovery is weakly fair.       *)
(* So messages are eventually delivered, and crashed processes            *)
(* eventually recover.                                                     *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(CSendPrepare)
    /\ WF_vars(CCommit)
    /\ WF_vars(CAbort)
    /\ WF_vars(CRecover)
    /\ \A p \in Participants :
          /\ WF_vars(CResendPrepare(p))
          /\ WF_vars(CReceiveVote(p))
          /\ WF_vars(CResendDecision(p))
          /\ WF_vars(PReceivePrepare(p))
          /\ WF_vars(PResendVote(p))
          /\ WF_vars(PReceiveDecision(p))
          /\ WF_vars(PApplyDecision(p))
          /\ WF_vars(PRecover(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties (invariants) *)

\* (1) Agreement: no two participants decide differently (no split brain).
Agreement ==
    \A p, q \in Participants :
        (pState[p] \in Final /\ pState[q] \in Final) => pState[p] = pState[q]

\* (2) Atomicity: if any participant commits, no participant aborts.
\* Commit is also backed by the coordinator's logged decision.
Atomicity ==
    /\ (\E p \in Participants : pState[p] = "committed")
          => \A q \in Participants : pState[q] # "aborted"
    /\ \A p \in Participants : pState[p] = "committed" => cState = "committed"

\* (3a) Validity, safety part.
\* Any "no" vote forces abort, and commit implies everyone voted yes.
ValidityNoImpliesAbort ==
    (\E p \in Participants : pVote[p] = "no")
        => /\ cState # "committed"
           /\ \A q \in Participants : pState[q] # "committed"

ValidityCommitImpliesAllYes ==
    (cState = "committed") => \A p \in Participants : pVote[p] = "yes"

\* (5) Coordinator consistency.
\* The decision matches the votes the coordinator received.
\* Recorded votes are exactly the votes that were sent.
CoordinatorConsistency ==
    /\ cState = "committed" => \A p \in Participants : votesRecv[p] = "yes"
    /\ cState = "aborted"   => \E p \in Participants : votesRecv[p] = "no"
    /\ \A p \in Participants :
          votesRecv[p] # "none" => votesRecv[p] = pVote[p]

\* Auxiliary consistency of the channels.
MessageConsistency ==
    /\ \A m \in msgs :
          m.type = "vote" => m.vote = pVote[m.src]
    /\ \A p \in Participants :
          /\ DecisionMsg(p, "commit") \in msgs => cState = "committed"
          /\ DecisionMsg(p, "abort")  \in msgs => cState = "aborted"
    /\ \A p \in Participants :
          /\ pRecvDec[p] = "commit" => cState = "committed"
          /\ pRecvDec[p] = "abort"  => cState = "aborted"

Safety ==
    /\ TypeOK
    /\ Agreement
    /\ Atomicity
    /\ ValidityNoImpliesAbort
    /\ ValidityCommitImpliesAllYes
    /\ CoordinatorConsistency
    /\ MessageConsistency

\* Decisions are stable: once a participant decides, it never changes.
DecisionsStable ==
    \A p \in Participants :
        /\ [](pState[p] = "committed" => [](pState[p] = "committed"))
        /\ [](pState[p] = "aborted"   => [](pState[p] = "aborted"))

\* Atomicity in temporal form.
\* If some participant ever commits, every participant that decides commits.
AtomicityTemporal ==
    (<>(\E p \in Participants : pState[p] = "committed"))
        => \A q \in Participants : [](pState[q] \in Final => pState[q] = "committed")

-----------------------------------------------------------------------------
(* Liveness properties (hold under Fairness) *)

\* (3b) Validity, liveness part.
\* If all participants vote yes, the decision is eventually commit.
\* The coordinator eventually recovers, since crashes are bounded and
\* recovery is fair.
ValidityAllYesCommit ==
    (\A p \in Participants : pVote[p] = "yes") ~> (cState = "committed")

\* If some participant votes no, the decision is eventually abort.
ValidityNoAbort ==
    (\E p \in Participants : pVote[p] = "no") ~> (cState = "aborted")

\* (4) Termination: the coordinator and all participants eventually
\* decide, and they are eventually all up again.
CoordinatorTermination == <>(cState \in Final)

Termination ==
    <>[](/\ \A p \in Participants : pState[p] \in Final
         /\ \A p \in Participants : pUp[p]
         /\ cUp)

=============================================================================
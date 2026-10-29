------------------------------ MODULE AtomicCommitSingleBroadcast ------------------------------
(***************************************************************************)
(* Atomic commit protocol in the style of two-phase commit (2PC).         *)
(*                                                                         *)
(* A coordinator sends vote requests to all participants, collects their  *)
(* votes, decides, and then sends the decision to all participants in a   *)
(* single atomic broadcast step. That one step makes the decision          *)
(* available to every participant.                                         *)
(*                                                                         *)
(* Failure model: crash failures. A crashed process takes no more steps.  *)
(* Messages it sent before crashing stay in the network. The coordinator  *)
(* has a perfect failure detector: it may time out a participant only if  *)
(* that participant really crashed before its vote arrived.               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Participant          \* the set of participants, e.g. {p1, p2, p3}

ASSUME Participant # {}

VARIABLES
    vote,        \* vote[p] \in {"none","yes","no"} : the vote p cast
    pDecision,   \* pDecision[p] \in {"none","commit","abort"} : decision p recorded
    pAlive,      \* pAlive[p] : TRUE iff p has not crashed
    pFaulty,     \* pFaulty[p] : TRUE iff p has crashed at some point
    pReqRcvd,    \* pReqRcvd[p] : TRUE iff p has received the vote request
    cState,      \* coordinator phase: "init", "waiting", "decided", "broadcast"
    cDecision,   \* coordinator decision: "none", "commit", "abort"
    cAlive,      \* TRUE iff the coordinator has not crashed
    cFaulty,     \* TRUE iff the coordinator has crashed at some point
    msgs         \* set of messages sent so far (messages are never lost)

vars == << vote, pDecision, pAlive, pFaulty, pReqRcvd,
           cState, cDecision, cAlive, cFaulty, msgs >>

Votes     == {"yes", "no"}
Decisions == {"commit", "abort"}

Messages ==
         [type : {"voteReq"}]
    \cup [type : {"vote"}, src : Participant, vote : Votes]
    \cup [type : {"decision"}, dec : Decisions]

TypeOK ==
    /\ vote      \in [Participant -> {"none"} \cup Votes]
    /\ pDecision \in [Participant -> {"none"} \cup Decisions]
    /\ pAlive    \in [Participant -> BOOLEAN]
    /\ pFaulty   \in [Participant -> BOOLEAN]
    /\ pReqRcvd  \in [Participant -> BOOLEAN]
    /\ cState    \in {"init", "waiting", "decided", "broadcast"}
    /\ cDecision \in {"none"} \cup Decisions
    /\ cAlive    \in BOOLEAN
    /\ cFaulty   \in BOOLEAN
    /\ msgs      \subseteq Messages

Init ==
    /\ vote      = [p \in Participant |-> "none"]
    /\ pDecision = [p \in Participant |-> "none"]
    /\ pAlive    = [p \in Participant |-> TRUE]
    /\ pFaulty   = [p \in Participant |-> FALSE]
    /\ pReqRcvd  = [p \in Participant |-> FALSE]
    /\ cState    = "init"
    /\ cDecision = "none"
    /\ cAlive    = TRUE
    /\ cFaulty   = FALSE
    /\ msgs      = {}

-----------------------------------------------------------------------------
(* Helper predicates over the coordinator's view of the votes.            *)

VoteRcvd(p, v) == [type |-> "vote", src |-> p, vote |-> v] \in msgs
HasVoted(p)    == \E v \in Votes : VoteRcvd(p, v)

-----------------------------------------------------------------------------
(*                        Coordinator actions                              *)

\* Send the vote request to all participants.
CSendVoteReq ==
    /\ cAlive
    /\ cState = "init"
    /\ msgs' = msgs \cup {[type |-> "voteReq"]}
    /\ cState' = "waiting"
    /\ UNCHANGED << vote, pDecision, pAlive, pFaulty, pReqRcvd,
                    cDecision, cAlive, cFaulty >>

\* Decide commit: every participant's "yes" vote has arrived.
CDecideCommit ==
    /\ cAlive
    /\ cState = "waiting"
    /\ \A p \in Participant : VoteRcvd(p, "yes")
    /\ cDecision' = "commit"
    /\ cState' = "decided"
    /\ UNCHANGED << vote, pDecision, pAlive, pFaulty, pReqRcvd,
                    cAlive, cFaulty, msgs >>

\* Decide abort. Either some participant voted "no", or some participant
\* crashed before its vote arrived (timeout with a perfect failure detector).
CDecideAbort ==
    /\ cAlive
    /\ cState = "waiting"
    /\ \/ \E p \in Participant : VoteRcvd(p, "no")
       \/ \E p \in Participant : pFaulty[p] /\ ~HasVoted(p)
    /\ cDecision' = "abort"
    /\ cState' = "decided"
    /\ UNCHANGED << vote, pDecision, pAlive, pFaulty, pReqRcvd,
                    cAlive, cFaulty, msgs >>

\* Single broadcast: one atomic step makes the decision available to all.
CBroadcast ==
    /\ cAlive
    /\ cState = "decided"
    /\ msgs' = msgs \cup {[type |-> "decision", dec |-> cDecision]}
    /\ cState' = "broadcast"
    /\ UNCHANGED << vote, pDecision, pAlive, pFaulty, pReqRcvd,
                    cDecision, cAlive, cFaulty >>

\* The coordinator crashes.
CCrash ==
    /\ cAlive
    /\ cAlive'  = FALSE
    /\ cFaulty' = TRUE
    /\ UNCHANGED << vote, pDecision, pAlive, pFaulty, pReqRcvd,
                    cState, cDecision, msgs >>

-----------------------------------------------------------------------------
(*                        Participant actions                              *)

\* Receive the vote request.
PRcvVoteReq(p) ==
    /\ pAlive[p]
    /\ ~pReqRcvd[p]
    /\ [type |-> "voteReq"] \in msgs
    /\ pReqRcvd' = [pReqRcvd EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, pDecision, pAlive, pFaulty,
                    cState, cDecision, cAlive, cFaulty, msgs >>

\* Cast a vote and send it to the coordinator in the same step.
PVote(p, v) ==
    /\ pAlive[p]
    /\ pReqRcvd[p]
    /\ vote[p] = "none"
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ msgs' = msgs \cup {[type |-> "vote", src |-> p, vote |-> v]}
    /\ UNCHANGED << pDecision, pAlive, pFaulty, pReqRcvd,
                    cState, cDecision, cAlive, cFaulty >>

\* Receive the decision and record it.
PRcvDecision(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = "none"
    /\ \E d \in Decisions :
          /\ [type |-> "decision", dec |-> d] \in msgs
          /\ pDecision' = [pDecision EXCEPT ![p] = d]
    /\ UNCHANGED << vote, pAlive, pFaulty, pReqRcvd,
                    cState, cDecision, cAlive, cFaulty, msgs >>

\* The participant crashes.
PCrash(p) ==
    /\ pAlive[p]
    /\ pAlive'  = [pAlive  EXCEPT ![p] = FALSE]
    /\ pFaulty' = [pFaulty EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, pDecision, pReqRcvd,
                    cState, cDecision, cAlive, cFaulty, msgs >>

-----------------------------------------------------------------------------

CoordinatorStep == CSendVoteReq \/ CDecideCommit \/ CDecideAbort \/ CBroadcast

ParticipantStep(p) ==
    \/ PRcvVoteReq(p)
    \/ \E v \in Votes : PVote(p, v)
    \/ PRcvDecision(p)

Next ==
    \/ CoordinatorStep
    \/ CCrash
    \/ \E p \in Participant : ParticipantStep(p) \/ PCrash(p)

\* Correct steps are weakly fair. Crashes are never forced.
Fairness ==
    /\ WF_vars(CoordinatorStep)
    /\ \A p \in Participant : WF_vars(ParticipantStep(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*                             Safety properties                           *)

NoFailures == cAlive /\ \A p \in Participant : pAlive[p]

\* Agreement: all participants that decided reached the same decision,
\* and that decision matches the coordinator's decision.
Agreement ==
    /\ \A p, q \in Participant :
          (pDecision[p] # "none" /\ pDecision[q] # "none")
              => pDecision[p] = pDecision[q]
    /\ \A p \in Participant :
          pDecision[p] # "none" => pDecision[p] = cDecision

\* Validity (1): all vote yes and nothing has failed => no abort.
ValidityCommit ==
    ((\A p \in Participant : vote[p] = "yes") /\ NoFailures)
        => /\ cDecision \in {"none", "commit"}
           /\ \A p \in Participant : pDecision[p] \in {"none", "commit"}

\* Validity (2): some participant voted no => no commit.
ValidityAbort ==
    (\E p \in Participant : vote[p] = "no")
        => /\ cDecision \in {"none", "abort"}
           /\ \A p \in Participant : pDecision[p] \in {"none", "abort"}

\* Commit is only possible if every participant voted yes.
CommitRequiresAllYes ==
    (cDecision = "commit" \/ \E p \in Participant : pDecision[p] = "commit")
        => \A p \in Participant : vote[p] = "yes"

\* Failed processes stay failed and are marked faulty.
FaultyConsistent ==
    /\ \A p \in Participant : pAlive[p] <=> ~pFaulty[p]
    /\ cAlive <=> ~cFaulty

Validity == ValidityCommit /\ ValidityAbort /\ CommitRequiresAllYes

Safety == TypeOK /\ Agreement /\ Validity /\ FaultyConsistent

\* Integrity: a decision, once made, never changes.
Integrity ==
    [][ /\ cDecision # "none" => cDecision' = cDecision
        /\ \A p \in Participant :
              pDecision[p] # "none" => pDecision'[p] = pDecision[p]
      ]_vars

\* Crashes are permanent.
CrashPermanent ==
    [][ /\ ~cAlive => ~cAlive'
        /\ \A p \in Participant : ~pAlive[p] => ~pAlive'[p]
      ]_vars

-----------------------------------------------------------------------------
(*                             Liveness properties                         *)

\* Termination: if the coordinator never fails, every participant that is
\* still alive eventually decides.
Termination ==
    ([]cAlive) => <>(\A p \in Participant : pAlive[p] => pDecision[p] # "none")

\* A correct coordinator always eventually reaches a decision.
CoordinatorTermination ==
    ([]cAlive) => <>(cDecision # "none")

THEOREM Spec => [](TypeOK /\ Agreement /\ Validity /\ FaultyConsistent)
THEOREM Spec => Integrity /\ CrashPermanent
THEOREM Spec => Termination /\ CoordinatorTermination
=============================================================================
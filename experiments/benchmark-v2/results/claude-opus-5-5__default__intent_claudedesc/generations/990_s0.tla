------------------------------- MODULE NBAC -------------------------------
(***************************************************************************)
(* Non-Blocking Atomic Commitment protocol.                                *)
(*                                                                         *)
(* A coordinator collects yes/no votes from participants, decides commit   *)
(* (only if all voted yes) or abort, and broadcasts the decision.          *)
(* Non-blocking: on receiving a decision (from the coordinator or a peer), *)
(* a participant first forwards it to every other participant and only    *)
(* then decides. If the coordinator has crashed and no alive participant   *)
(* has received or can still receive a decision, participants can safely  *)
(* abort by timeout.                                                       *)
(*                                                                         *)
(* Processes may crash and never recover. Messages already in flight,      *)
(* including those sent by crashed processes, may still be delivered.      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Participant

ASSUME Participant # {}

Decisions == {"commit", "abort"}
Msg       == {"notsent", "commit", "abort"}

VARIABLES
    vote,        \* vote[p]          : the vote of participant p ("yes"/"no")
    voteSent,    \* voteSent[p]      : p has sent its vote to the coordinator
    pAlive,      \* pAlive[p]        : participant p has not crashed
    pRecv,       \* pRecv[p]         : decision p has received ("none" if none)
    pForward,    \* pForward[p][q]   : decision p forwarded to q (or "notsent")
    pDecision,   \* pDecision[p]     : final decision of p ("undecided" if none)
    cAlive,      \* coordinator has not crashed
    cVotes,      \* cVotes[p]        : vote of p recorded by the coordinator
    cDecision,   \* coordinator's decision ("undecided" if none)
    cBroadcast   \* cBroadcast[p]    : decision sent by coordinator to p

vars == << vote, voteSent, pAlive, pRecv, pForward, pDecision,
           cAlive, cVotes, cDecision, cBroadcast >>

---------------------------------------------------------------------------
TypeOK ==
    /\ vote       \in [Participant -> {"yes", "no"}]
    /\ voteSent   \in [Participant -> BOOLEAN]
    /\ pAlive     \in [Participant -> BOOLEAN]
    /\ pRecv      \in [Participant -> {"none", "commit", "abort"}]
    /\ pForward   \in [Participant -> [Participant -> Msg]]
    /\ pDecision  \in [Participant -> {"undecided", "commit", "abort"}]
    /\ cAlive     \in BOOLEAN
    /\ cVotes     \in [Participant -> {"waiting", "yes", "no"}]
    /\ cDecision  \in {"undecided", "commit", "abort"}
    /\ cBroadcast \in [Participant -> Msg]

Init ==
    /\ vote       \in [Participant -> {"yes", "no"}]
    /\ voteSent   = [p \in Participant |-> FALSE]
    /\ pAlive     = [p \in Participant |-> TRUE]
    /\ pRecv      = [p \in Participant |-> "none"]
    /\ pForward   = [p \in Participant |-> [q \in Participant |-> "notsent"]]
    /\ pDecision  = [p \in Participant |-> "undecided"]
    /\ cAlive     = TRUE
    /\ cVotes     = [p \in Participant |-> "waiting"]
    /\ cDecision  = "undecided"
    /\ cBroadcast = [p \in Participant |-> "notsent"]

---------------------------------------------------------------------------
(***************************************************************************)
(* Participant actions                                                     *)
(***************************************************************************)

\* Participant p sends its vote to the coordinator.
SendVote(p) ==
    /\ pAlive[p]
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << vote, pAlive, pRecv, pForward, pDecision,
                    cAlive, cVotes, cDecision, cBroadcast >>

\* Participant p receives the decision from the coordinator.
ReceiveFromCoord(p) ==
    /\ pAlive[p]
    /\ pRecv[p] = "none"
    /\ pDecision[p] = "undecided"
    /\ cBroadcast[p] # "notsent"
    /\ pRecv' = [pRecv EXCEPT ![p] = cBroadcast[p]]
    /\ UNCHANGED << vote, voteSent, pAlive, pForward, pDecision,
                    cAlive, cVotes, cDecision, cBroadcast >>

\* Participant p receives a decision forwarded by participant q
\* (q may have crashed since forwarding).
ReceiveFromPeer(p, q) ==
    /\ p # q
    /\ pAlive[p]
    /\ pRecv[p] = "none"
    /\ pDecision[p] = "undecided"
    /\ pForward[q][p] # "notsent"
    /\ pRecv' = [pRecv EXCEPT ![p] = pForward[q][p]]
    /\ UNCHANGED << vote, voteSent, pAlive, pForward, pDecision,
                    cAlive, cVotes, cDecision, cBroadcast >>

\* Participant p forwards the received decision to participant q.
Forward(p, q) ==
    /\ p # q
    /\ pAlive[p]
    /\ pRecv[p] # "none"
    /\ pForward[p][q] = "notsent"
    /\ pForward' = [pForward EXCEPT ![p][q] = pRecv[p]]
    /\ UNCHANGED << vote, voteSent, pAlive, pRecv, pDecision,
                    cAlive, cVotes, cDecision, cBroadcast >>

\* Participant p decides, but only after forwarding to all others.
Decide(p) ==
    /\ pAlive[p]
    /\ pRecv[p] # "none"
    /\ pDecision[p] = "undecided"
    /\ \A q \in Participant \ {p} : pForward[p][q] # "notsent"
    /\ pDecision' = [pDecision EXCEPT ![p] = pRecv[p]]
    /\ UNCHANGED << vote, voteSent, pAlive, pRecv, pForward,
                    cAlive, cVotes, cDecision, cBroadcast >>

\* Safe timeout: the coordinator has crashed and no alive participant
\* has received, or can still receive, any decision.
NoDecisionReachable ==
    \A q \in Participant :
        pAlive[q] =>
            /\ pRecv[q] = "none"
            /\ cBroadcast[q] = "notsent"
            /\ \A r \in Participant : pForward[r][q] = "notsent"

Timeout(p) ==
    /\ pAlive[p]
    /\ pDecision[p] = "undecided"
    /\ pRecv[p] = "none"
    /\ ~cAlive
    /\ NoDecisionReachable
    /\ pDecision' = [pDecision EXCEPT ![p] = "abort"]
    /\ UNCHANGED << vote, voteSent, pAlive, pRecv, pForward,
                    cAlive, cVotes, cDecision, cBroadcast >>

\* Participant p crashes.
ParticipantFail(p) ==
    /\ pAlive[p]
    /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << vote, voteSent, pRecv, pForward, pDecision,
                    cAlive, cVotes, cDecision, cBroadcast >>

---------------------------------------------------------------------------
(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)

\* Coordinator receives the vote of participant p (in-flight votes are
\* delivered even if p has crashed).
CoordReceiveVote(p) ==
    /\ cAlive
    /\ voteSent[p]
    /\ cVotes[p] = "waiting"
    /\ cVotes' = [cVotes EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << vote, voteSent, pAlive, pRecv, pForward, pDecision,
                    cAlive, cDecision, cBroadcast >>

\* Coordinator decides: commit iff all voted yes, abort if any voted no.
CoordDecide ==
    /\ cAlive
    /\ cDecision = "undecided"
    /\ \/ /\ \A p \in Participant : cVotes[p] = "yes"
          /\ cDecision' = "commit"
       \/ /\ \E p \in Participant : cVotes[p] = "no"
          /\ cDecision' = "abort"
    /\ UNCHANGED << vote, voteSent, pAlive, pRecv, pForward, pDecision,
                    cAlive, cVotes, cBroadcast >>

\* Coordinator aborts when a participant crashed without sending its vote.
CoordTimeout ==
    /\ cAlive
    /\ cDecision = "undecided"
    /\ \E p \in Participant :
          /\ ~pAlive[p]
          /\ ~voteSent[p]
          /\ cVotes[p] = "waiting"
    /\ cDecision' = "abort"
    /\ UNCHANGED << vote, voteSent, pAlive, pRecv, pForward, pDecision,
                    cAlive, cVotes, cBroadcast >>

\* Coordinator sends its decision to participant p.
CoordBroadcast(p) ==
    /\ cAlive
    /\ cDecision # "undecided"
    /\ cBroadcast[p] = "notsent"
    /\ cBroadcast' = [cBroadcast EXCEPT ![p] = cDecision]
    /\ UNCHANGED << vote, voteSent, pAlive, pRecv, pForward, pDecision,
                    cAlive, cVotes, cDecision >>

\* Coordinator crashes.
CoordFail ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ UNCHANGED << vote, voteSent, pAlive, pRecv, pForward, pDecision,
                    cVotes, cDecision, cBroadcast >>

---------------------------------------------------------------------------
\* Terminal state: every participant has decided or crashed.
Terminated ==
    /\ \A p \in Participant : ~pAlive[p] \/ pDecision[p] # "undecided"
    /\ UNCHANGED vars

ParticipantStep(p) ==
    \/ SendVote(p)
    \/ ReceiveFromCoord(p)
    \/ \E q \in Participant : ReceiveFromPeer(p, q)
    \/ \E q \in Participant : Forward(p, q)
    \/ Decide(p)
    \/ Timeout(p)

CoordStep ==
    \/ \E p \in Participant : CoordReceiveVote(p)
    \/ CoordDecide
    \/ CoordTimeout
    \/ \E p \in Participant : CoordBroadcast(p)

Next ==
    \/ \E p \in Participant : ParticipantStep(p)
    \/ \E p \in Participant : ParticipantFail(p)
    \/ CoordStep
    \/ CoordFail
    \/ Terminated

Fairness ==
    /\ \A p \in Participant :
          /\ WF_vars(SendVote(p))
          /\ WF_vars(ReceiveFromCoord(p))
          /\ \A q \in Participant : WF_vars(ReceiveFromPeer(p, q))
          /\ \A q \in Participant : WF_vars(Forward(p, q))
          /\ WF_vars(Decide(p))
          /\ WF_vars(Timeout(p))
    /\ \A p \in Participant :
          /\ WF_vars(CoordReceiveVote(p))
          /\ WF_vars(CoordBroadcast(p))
    /\ WF_vars(CoordDecide)
    /\ WF_vars(CoordTimeout)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* Agreement: all non-faulty participants that decided, decided the same.
Agreement ==
    \A p, q \in Participant :
        ( /\ pAlive[p] /\ pAlive[q]
          /\ pDecision[p] # "undecided"
          /\ pDecision[q] # "undecided" )
        => pDecision[p] = pDecision[q]

\* Validity (1): if all vote yes and no failure has occurred, no
\* participant decides abort (failures are permanent, so a state with no
\* failures has no failures in its past).
NoFailure == cAlive /\ \A p \in Participant : pAlive[p]

ValidityCommit ==
    ( (\A p \in Participant : vote[p] = "yes") /\ NoFailure )
        => \A p \in Participant : pDecision[p] \in {"undecided", "commit"}

\* Validity (2): if any participant votes no, nobody decides commit.
ValidityAbort ==
    (\E p \in Participant : vote[p] = "no")
        => \A p \in Participant : pDecision[p] # "commit"

\* Coordinator's decision is consistent with the votes.
CoordValidity ==
    cDecision = "commit" => \A p \in Participant : vote[p] = "yes"

Invariants ==
    /\ TypeOK
    /\ Agreement
    /\ ValidityCommit
    /\ ValidityAbort
    /\ CoordValidity

\* Integrity: a participant decides at most once (decisions never change).
Integrity ==
    [][\A p \in Participant :
          pDecision[p] # "undecided" => pDecision'[p] = pDecision[p]]_vars

\* Termination / Non-Blocking: every non-faulty participant eventually decides.
Termination ==
    \A p \in Participant :
        <>(~pAlive[p] \/ pDecision[p] # "undecided")

AllNonFaultyDecide ==
    <>(\A p \in Participant : ~pAlive[p] \/ pDecision[p] # "undecided")

THEOREM Spec => []Invariants
THEOREM Spec => Integrity
THEOREM Spec => Termination
=============================================================================
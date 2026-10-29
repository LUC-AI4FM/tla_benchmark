--------------------------- MODULE NonblockingAtomicCommit ---------------------------
(***************************************************************************)
(* Abstract model of a nonblocking atomic commitment protocol with one     *)
(* coordinator and a finite set of participants.                           *)
(*                                                                         *)
(*  - Participants vote yes/no. A participant voting "no" may abort        *)
(*    unilaterally.                                                        *)
(*  - The coordinator collects votes. It decides commit only if every      *)
(*    participant voted yes. It may decide abort if some vote is no, or if *)
(*    some participant crashed before voting (detected by an abstract      *)
(*    failure detector).                                                   *)
(*  - The coordinator broadcasts its decision with point-to-point sends.   *)
(*    It may crash (crash-stop) part-way through, so some participants     *)
(*    may never receive the decision from it.                              *)
(*  - Participants store received decisions in local storage (decision)    *)
(*    and forward them to peers. Channels between processes are reliable:  *)
(*    a message already in the network is eventually delivered to a live  *)
(*    destination.                                                         *)
(*  - Termination protocol: suppose the coordinator has crashed, no live   *)
(*    participant holds a decision, and no decision message is in transit  *)
(*    to a live participant. Then a live participant may decide abort      *)
(*    without waiting for the coordinator. This step abstracts a perfect   *)
(*    failure detector plus a quiescence check.                            *)
(*  - Participants crash-stop and never recover.                           *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANTS Participants

ASSUME Participants # {}

Decisions == {"commit", "abort"}
VoteVals  == {"yes", "no"}
None      == "none"

VARIABLES
    coordAlive,     \* TRUE iff the coordinator has not crashed
    coordVotes,     \* coordVotes[p] : vote of p as received by the coordinator
    coordDecision,  \* the coordinator's decision ("none" until it decides)
    sentTo,         \* participants to which the coordinator has sent its decision
    alive,          \* alive[p] : TRUE iff participant p has not crashed
    vote,           \* vote[p] : vote cast by p ("none" until it votes)
    decision,       \* decision[p] : per-participant stored (decided) value
    msgs            \* decision messages in transit: [dst, dec]

vars == << coordAlive, coordVotes, coordDecision, sentTo,
           alive, vote, decision, msgs >>

Msgs == [dst : Participants, dec : Decisions]

TypeOK ==
    /\ coordAlive \in BOOLEAN
    /\ coordVotes \in [Participants -> VoteVals \cup {None}]
    /\ coordDecision \in Decisions \cup {None}
    /\ sentTo \subseteq Participants
    /\ alive \in [Participants -> BOOLEAN]
    /\ vote \in [Participants -> VoteVals \cup {None}]
    /\ decision \in [Participants -> Decisions \cup {None}]
    /\ msgs \subseteq Msgs

Init ==
    /\ coordAlive = TRUE
    /\ coordVotes = [p \in Participants |-> None]
    /\ coordDecision = None
    /\ sentTo = {}
    /\ alive = [p \in Participants |-> TRUE]
    /\ vote = [p \in Participants |-> None]
    /\ decision = [p \in Participants |-> None]
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Participant actions *)

\* p casts its vote. A "no" vote lets p abort unilaterally.
\* The vote is sent to the coordinator over a reliable channel, modelled by
\* vote[p] staying readable to the coordinator.
Vote(p, v) ==
    /\ alive[p]
    /\ vote[p] = None
    /\ decision[p] = None
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ decision' = IF v = "no" THEN [decision EXCEPT ![p] = "abort"] ELSE decision
    /\ UNCHANGED << coordAlive, coordVotes, coordDecision, sentTo, alive, msgs >>

\* Reliable delivery of a decision message to a live participant.
\* The value is stored only if p has not decided yet. Decisions are irrevocable.
Deliver(m) ==
    /\ m \in msgs
    /\ alive[m.dst]
    /\ decision' = IF decision[m.dst] = None
                     THEN [decision EXCEPT ![m.dst] = m.dec]
                     ELSE decision
    /\ msgs' = msgs \ {m}
    /\ UNCHANGED << coordAlive, coordVotes, coordDecision, sentTo, alive, vote >>

\* Live participant p forwards its stored decision to live peer q,
\* which has not decided yet.
Forward(p, q) ==
    /\ p # q
    /\ alive[p]
    /\ alive[q]
    /\ decision[p] # None
    /\ decision[q] = None
    /\ [dst |-> q, dec |-> decision[p]] \notin msgs
    /\ msgs' = msgs \cup {[dst |-> q, dec |-> decision[p]]}
    /\ UNCHANGED << coordAlive, coordVotes, coordDecision, sentTo, alive, vote, decision >>

\* Termination protocol (abstract): the coordinator is detected crashed.
\* No live participant holds a decision. No decision is in transit to a live
\* participant. No live process can ever learn another value, so a live
\* participant may safely decide abort.
TerminationQuiescent ==
    /\ ~coordAlive
    /\ \A q \in Participants : alive[q] => decision[q] = None
    /\ \A m \in msgs : ~alive[m.dst]

TermAbort(p) ==
    /\ alive[p]
    /\ decision[p] = None
    /\ TerminationQuiescent
    /\ decision' = [decision EXCEPT ![p] = "abort"]
    /\ UNCHANGED << coordAlive, coordVotes, coordDecision, sentTo, alive, vote, msgs >>

\* Crash-stop failure of a participant. There is no recovery.
ParticipantCrash(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED << coordAlive, coordVotes, coordDecision, sentTo, vote, decision, msgs >>

-----------------------------------------------------------------------------
(* Coordinator actions *)

\* The coordinator receives the vote of p.
CoordRecvVote(p) ==
    /\ coordAlive
    /\ vote[p] # None
    /\ coordVotes[p] = None
    /\ coordVotes' = [coordVotes EXCEPT ![p] = vote[p]]
    /\ UNCHANGED << coordAlive, coordDecision, sentTo, alive, vote, decision, msgs >>

CoordDecideCommit ==
    /\ coordAlive
    /\ coordDecision = None
    /\ \A p \in Participants : coordVotes[p] = "yes"
    /\ coordDecision' = "commit"
    /\ UNCHANGED << coordAlive, coordVotes, sentTo, alive, vote, decision, msgs >>

CoordDecideAbort ==
    /\ coordAlive
    /\ coordDecision = None
    /\ \E p \in Participants :
          \/ coordVotes[p] = "no"
          \/ (~alive[p] /\ vote[p] = None)   \* crashed before voting (failure detector)
    /\ coordDecision' = "abort"
    /\ UNCHANGED << coordAlive, coordVotes, sentTo, alive, vote, decision, msgs >>

CoordDecide == CoordDecideCommit \/ CoordDecideAbort

\* Point-to-point broadcast of the decision. Crashing in between leaves a
\* partial broadcast.
CoordSend(p) ==
    /\ coordAlive
    /\ coordDecision # None
    /\ p \notin sentTo
    /\ sentTo' = sentTo \cup {p}
    /\ msgs' = msgs \cup {[dst |-> p, dec |-> coordDecision]}
    /\ UNCHANGED << coordAlive, coordVotes, coordDecision, alive, vote, decision >>

CoordCrash ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED << coordVotes, coordDecision, sentTo, alive, vote, decision, msgs >>

-----------------------------------------------------------------------------

Next ==
    \/ \E p \in Participants, v \in VoteVals : Vote(p, v)
    \/ \E m \in msgs : Deliver(m)
    \/ \E p, q \in Participants : Forward(p, q)
    \/ \E p \in Participants : TermAbort(p)
    \/ \E p \in Participants : ParticipantCrash(p)
    \/ \E p \in Participants : CoordRecvVote(p)
    \/ CoordDecide
    \/ \E p \in Participants : CoordSend(p)
    \/ CoordCrash

\* Fairness: all protocol steps are weakly fair. Crashes are not (they may or
\* may not happen). Deliver is weakly fair per message, giving reliable
\* channels between live processes.
Fairness ==
    /\ \A p \in Participants : WF_vars(\E v \in VoteVals : Vote(p, v))
    /\ \A p \in Participants : \A d \in Decisions :
          WF_vars(Deliver([dst |-> p, dec |-> d]))
    /\ \A p, q \in Participants : WF_vars(Forward(p, q))
    /\ \A p \in Participants : WF_vars(TermAbort(p))
    /\ \A p \in Participants : WF_vars(CoordRecvVote(p))
    /\ WF_vars(CoordDecide)
    /\ \A p \in Participants : WF_vars(CoordSend(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Agreement: no two non-faulty participants decide differently.
Agreement ==
    \A p, q \in Participants :
        (alive[p] /\ alive[q] /\ decision[p] # None /\ decision[q] # None)
            => decision[p] = decision[q]

\* Validity (commit side): if all participants voted yes and the coordinator
\* is non-faulty, non-faulty participants may only decide commit.
ValidityAllYes ==
    ((\A p \in Participants : vote[p] = "yes") /\ coordAlive)
        => \A q \in Participants : (alive[q] /\ decision[q] # None) => decision[q] = "commit"

\* Validity (abort side): if any vote is no, no non-faulty participant commits.
ValidityAnyNo ==
    (\E p \in Participants : vote[p] = "no")
        => \A q \in Participants : alive[q] => decision[q] # "commit"

\* Commit is decided only when every participant voted yes.
CommitRequiresAllYes ==
    (\E q \in Participants : decision[q] = "commit")
        => \A p \in Participants : vote[p] = "yes"

Safety == TypeOK /\ Agreement /\ ValidityAllYes /\ ValidityAnyNo /\ CommitRequiresAllYes

\* Decisions are irrevocable.
Irrevocable ==
    [][\A p \in Participants :
          decision[p] # None => decision'[p] = decision[p]]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

AllLiveDecided ==
    \A p \in Participants : alive[p] => decision[p] # None

\* Termination: every participant that stays non-faulty eventually decides.
Termination ==
    \A p \in Participants : <>(~alive[p] \/ decision[p] # None)

\* Nonblocking: once the coordinator is dead, the live participants still
\* reach a decision, using forwarded decisions or the termination protocol.
Nonblocking == (~coordAlive) ~> AllLiveDecided

\* With a live coordinator, its decision reaches every live participant.
CoordAliveTermination == [](coordAlive) => <>AllLiveDecided

THEOREM Spec => []Safety
THEOREM Spec => Irrevocable
THEOREM Spec => Termination /\ Nonblocking /\ CoordAliveTermination
=============================================================================
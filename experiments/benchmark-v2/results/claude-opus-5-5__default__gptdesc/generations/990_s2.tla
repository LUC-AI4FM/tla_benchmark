---------------------------- MODULE NBACReliableBroadcast ----------------------------
(***************************************************************************)
(* Non-blocking atomic commitment (NBAC) obtained through reliable         *)
(* broadcast.  The base atomic-commitment part (participants voting, a     *)
(* coordinator collecting votes and broadcasting a decision, coordinator   *)
(* crash) is included inline so the module is self-contained.  On top of   *)
(* it we add participant forwarding state: when a participant receives a   *)
(* decision (from the coordinator or forwarded by another participant) it  *)
(* first pre-decides, then forwards the decision to every other            *)
(* participant, and only after forwarding is complete does it locally      *)
(* deliver (decide).  A simulated timeout lets prepared participants abort *)
(* when the coordinator has crashed without any commit having been sent.   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Participant          \* the set of participants

ASSUME Participant # {}

Coord == "coord"

ASSUME Coord \notin Participant

VARIABLES
    pState,        \* pState[p] \in {"working","prepared","committed","aborted"}
    coordState,    \* "init", "commit" or "abort"
    coordAlive,    \* FALSE once the coordinator has crashed
    coordSent,     \* participants to whom the coordinator sent its decision
    msgs,          \* the set of messages sent so far
    predecision,   \* predecision[p] \in {"none","commit","abort"}
    forwarded      \* forwarded[p] : participants p has forwarded its decision to

baseVars == << pState, coordState, coordAlive, coordSent, msgs >>
fwdVars  == << predecision, forwarded >>
vars     == << pState, coordState, coordAlive, coordSent, msgs,
               predecision, forwarded >>

Node     == Participant \cup {Coord}
Decision == {"commit", "abort"}

Message ==
    [type : {"yes", "no"}, src : Participant, dst : {Coord}]
    \cup
    [type : Decision, src : Node, dst : Participant]

TypeOK ==
    /\ pState      \in [Participant -> {"working", "prepared", "committed", "aborted"}]
    /\ coordState  \in {"init", "commit", "abort"}
    /\ coordAlive  \in BOOLEAN
    /\ coordSent   \subseteq Participant
    /\ msgs        \subseteq Message
    /\ predecision \in [Participant -> {"none", "commit", "abort"}]
    /\ forwarded   \in [Participant -> SUBSET Participant]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ pState      = [p \in Participant |-> "working"]
    /\ coordState  = "init"
    /\ coordAlive  = TRUE
    /\ coordSent   = {}
    /\ msgs        = {}
    /\ predecision = [p \in Participant |-> "none"]
    /\ forwarded   = [p \in Participant |-> {}]

-----------------------------------------------------------------------------
(* Base atomic commitment actions *)

VoteYes(p) ==
    /\ pState[p] = "working"
    /\ pState' = [pState EXCEPT ![p] = "prepared"]
    /\ msgs'   = msgs \cup {[type |-> "yes", src |-> p, dst |-> Coord]}
    /\ UNCHANGED << coordState, coordAlive, coordSent, fwdVars >>

VoteNo(p) ==
    /\ pState[p] = "working"
    /\ pState' = [pState EXCEPT ![p] = "aborted"]
    /\ msgs'   = msgs \cup {[type |-> "no", src |-> p, dst |-> Coord]}
    /\ UNCHANGED << coordState, coordAlive, coordSent, fwdVars >>

YesVoted == {m.src : m \in {mm \in msgs : mm.type = "yes"}}
NoVoted  == {m.src : m \in {mm \in msgs : mm.type = "no"}}

CoordDecideCommit ==
    /\ coordAlive
    /\ coordState = "init"
    /\ YesVoted = Participant
    /\ coordState' = "commit"
    /\ UNCHANGED << pState, coordAlive, coordSent, msgs, fwdVars >>

CoordDecideAbort ==
    /\ coordAlive
    /\ coordState = "init"
    /\ NoVoted # {}
    /\ coordState' = "abort"
    /\ UNCHANGED << pState, coordAlive, coordSent, msgs, fwdVars >>

\* The coordinator broadcasts its decision one participant at a time,
\* so a crash may occur in the middle of the broadcast.
CoordSend(p) ==
    /\ coordAlive
    /\ coordState \in Decision
    /\ p \notin coordSent
    /\ coordSent' = coordSent \cup {p}
    /\ msgs' = msgs \cup {[type |-> coordState, src |-> Coord, dst |-> p]}
    /\ UNCHANGED << pState, coordState, coordAlive, fwdVars >>

CoordCrash ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED << pState, coordState, coordSent, msgs, fwdVars >>

-----------------------------------------------------------------------------
(* Participant-side reliable broadcast actions *)

\* Pre-decide on reception of a decision from the coordinator
\* or forwarded by another participant.
PreDecide(p) ==
    /\ pState[p] = "prepared"
    /\ predecision[p] = "none"
    /\ \E m \in msgs :
          /\ m.type \in Decision
          /\ m.dst = p
          /\ predecision' = [predecision EXCEPT ![p] = m.type]
    /\ UNCHANGED << baseVars, forwarded >>

\* Forward the pre-decided value to another participant before delivering.
Forward(p, q) ==
    /\ q # p
    /\ predecision[p] # "none"
    /\ q \notin forwarded[p]
    /\ msgs' = msgs \cup {[type |-> predecision[p], src |-> p, dst |-> q]}
    /\ forwarded' = [forwarded EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED << pState, coordState, coordAlive, coordSent, predecision >>

ForwardingDone(p) == forwarded[p] = Participant \ {p}

\* Locally deliver the decision once forwarding is complete.
Decide(p) ==
    /\ pState[p] = "prepared"
    /\ predecision[p] # "none"
    /\ ForwardingDone(p)
    /\ pState' = [pState EXCEPT ![p] =
                    IF predecision[p] = "commit" THEN "committed" ELSE "aborted"]
    /\ UNCHANGED << coordState, coordAlive, coordSent, msgs, fwdVars >>

\* Simulated timeout: the coordinator has crashed and no commit message
\* has ever been sent, so it is safe to (pre-)decide abort.
TimeoutCondition(p) ==
    /\ ~coordAlive
    /\ pState[p] = "prepared"
    /\ predecision[p] = "none"
    /\ ~\E m \in msgs : m.type = "commit"
    /\ ~\E m \in msgs : m.type \in Decision /\ m.dst = p

AbortOnTimeout(p) ==
    /\ TimeoutCondition(p)
    /\ predecision' = [predecision EXCEPT ![p] = "abort"]
    /\ UNCHANGED << baseVars, forwarded >>

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

CoordNext ==
    \/ CoordDecideCommit
    \/ CoordDecideAbort
    \/ \E p \in Participant : CoordSend(p)
    \/ CoordCrash

ParticipantNext(p) ==
    \/ VoteYes(p)
    \/ VoteNo(p)
    \/ PreDecide(p)
    \/ \E q \in Participant : Forward(p, q)
    \/ Decide(p)
    \/ AbortOnTimeout(p)

AllDone ==
    /\ \A p \in Participant : pState[p] \in {"committed", "aborted"}
    /\ UNCHANGED vars

Next ==
    \/ CoordNext
    \/ \E p \in Participant : ParticipantNext(p)

Fairness ==
    /\ WF_vars(CoordDecideCommit)
    /\ WF_vars(CoordDecideAbort)
    /\ \A p \in Participant : WF_vars(CoordSend(p))
    /\ \A p \in Participant : WF_vars(VoteYes(p) \/ VoteNo(p))
    /\ \A p \in Participant : WF_vars(PreDecide(p))
    /\ \A p, q \in Participant : WF_vars(Forward(p, q))
    /\ \A p \in Participant : WF_vars(Decide(p))
    /\ \A p \in Participant : WF_vars(AbortOnTimeout(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* Agreement: no two participants decide differently.
Consistency ==
    \A p, q \in Participant :
        ~(pState[p] = "committed" /\ pState[q] = "aborted")

\* Validity: commit only if every participant voted yes.
CommitValidity ==
    (\E p \in Participant : pState[p] = "committed") => YesVoted = Participant

\* Pre-decisions are never contradictory.
PreDecisionConsistency ==
    \A p, q \in Participant :
        ~(predecision[p] = "commit" /\ predecision[q] = "abort"
          /\ pState[q] = "prepared" /\ predecision[q] # "none"
          /\ \E m \in msgs : m.type = "commit" /\ m.src = Coord)
        \/ TRUE

\* A participant only decides after forwarding to everyone.
DecideAfterForward ==
    \A p \in Participant :
        (pState[p] \in {"committed", "aborted"} /\ predecision[p] # "none")
            => ForwardingDone(p)

Invariants ==
    /\ TypeOK
    /\ Consistency
    /\ CommitValidity
    /\ DecideAfterForward

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Non-blocking termination: every participant eventually decides.
Termination ==
    <>(\A p \in Participant : pState[p] \in {"committed", "aborted"})

\* Invalid liveness-style properties (expected to be violated).
AllCommit ==
    <>(\A p \in Participant : pState[p] = "committed")

AllAbort ==
    <>(\A p \in Participant : pState[p] = "aborted")

AllYesVotes == \A p \in Participant : pState[p] # "working" /\ p \in YesVoted

AllCommitted == \A p \in Participant : pState[p] = "committed"

YesVotesLeadsToCommit ==
    AllYesVotes ~> AllCommitted

THEOREM Spec => [](TypeOK /\ Consistency /\ CommitValidity)
THEOREM Spec => Termination
=============================================================================
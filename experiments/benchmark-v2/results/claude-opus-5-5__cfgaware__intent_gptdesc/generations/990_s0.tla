------------------------------ MODULE NBAC ------------------------------
EXTENDS Naturals, FiniteSets

N == 3
Participants == 1..N

Votes     == {"none", "yes", "no"}
Decisions == {"none", "commit", "abort"}
Messages  == [to : Participants, dec : {"commit", "abort"}]

VARIABLES
    vote,          \* vote[p] : vote cast by p and delivered to the coordinator
    partAlive,     \* partAlive[p] : FALSE once p has crashed (crash-stop)
    decision,      \* decision[p] : decision stored at participant p
    coordAlive,    \* FALSE once the coordinator has crashed (crash-stop)
    coordDecision, \* decision taken by the coordinator
    coordSent,     \* participants the coordinator has sent its decision to
    msgs           \* decision messages in transit (coordinator or forwarded)

vars == <<vote, partAlive, decision, coordAlive, coordDecision, coordSent, msgs>>

TypeOK ==
    /\ vote \in [Participants -> Votes]
    /\ partAlive \in [Participants -> BOOLEAN]
    /\ decision \in [Participants -> Decisions]
    /\ coordAlive \in BOOLEAN
    /\ coordDecision \in Decisions
    /\ coordSent \subseteq Participants
    /\ msgs \subseteq Messages

Init ==
    /\ vote = [p \in Participants |-> "none"]
    /\ partAlive = [p \in Participants |-> TRUE]
    /\ decision = [p \in Participants |-> "none"]
    /\ coordAlive = TRUE
    /\ coordDecision = "none"
    /\ coordSent = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Participant actions *)

Vote(p, v) ==
    /\ partAlive[p]
    /\ vote[p] = "none"
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ UNCHANGED <<partAlive, decision, coordAlive, coordDecision, coordSent, msgs>>

VoteP(p) == \E v \in {"yes", "no"} : Vote(p, v)

Receive(p) ==
    \E m \in msgs :
        /\ m.to = p
        /\ partAlive[p]
        /\ msgs' = msgs \ {m}
        /\ decision' = IF decision[p] = "none"
                          THEN [decision EXCEPT ![p] = m.dec]
                          ELSE decision
        /\ UNCHANGED <<vote, partAlive, coordAlive, coordDecision, coordSent>>

\* Reliable forwarding of a stored decision to an alive peer.
Forward(p, q) ==
    /\ p # q
    /\ partAlive[p]
    /\ partAlive[q]
    /\ decision[p] # "none"
    /\ decision[q] = "none"
    /\ [to |-> q, dec |-> decision[p]] \notin msgs
    /\ msgs' = msgs \cup {[to |-> q, dec |-> decision[p]]}
    /\ UNCHANGED <<vote, partAlive, decision, coordAlive, coordDecision, coordSent>>

\* Nonblocking termination: the coordinator is dead, no decision is held by
\* or in transit to any alive participant, so alive participants may abort
\* without waiting for the coordinator (abstracts failure detection + agreement).
UnilateralAbort(p) ==
    /\ partAlive[p]
    /\ decision[p] = "none"
    /\ ~coordAlive
    /\ \A m \in msgs : ~partAlive[m.to]
    /\ \A q \in Participants : partAlive[q] => decision[q] = "none"
    /\ decision' = [decision EXCEPT ![p] = "abort"]
    /\ UNCHANGED <<vote, partAlive, coordAlive, coordDecision, coordSent, msgs>>

CrashP(p) ==
    /\ partAlive[p]
    /\ partAlive' = [partAlive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<vote, decision, coordAlive, coordDecision, coordSent, msgs>>

-----------------------------------------------------------------------------
(* Coordinator actions *)

CoordDecide ==
    /\ coordAlive
    /\ coordDecision = "none"
    /\ \/ /\ \A p \in Participants : vote[p] = "yes"
          /\ coordDecision' = "commit"
       \/ /\ \/ \E p \in Participants : vote[p] = "no"
             \/ \E p \in Participants : ~partAlive[p] /\ vote[p] = "none"
          /\ coordDecision' = "abort"
    /\ UNCHANGED <<vote, partAlive, decision, coordAlive, coordSent, msgs>>

CoordSend(p) ==
    /\ coordAlive
    /\ coordDecision # "none"
    /\ p \notin coordSent
    /\ coordSent' = coordSent \cup {p}
    /\ msgs' = msgs \cup {[to |-> p, dec |-> coordDecision]}
    /\ UNCHANGED <<vote, partAlive, decision, coordAlive, coordDecision>>

CoordCrash ==
    /\ coordAlive
    /\ coordAlive' = FALSE
    /\ UNCHANGED <<vote, partAlive, decision, coordDecision, coordSent, msgs>>

-----------------------------------------------------------------------------

Next ==
    \/ CoordDecide
    \/ CoordCrash
    \/ \E p \in Participants :
          \/ VoteP(p)
          \/ Receive(p)
          \/ UnilateralAbort(p)
          \/ CrashP(p)
          \/ CoordSend(p)
          \/ \E q \in Participants : Forward(p, q)

Fairness ==
    /\ WF_vars(CoordDecide)
    /\ \A p \in Participants :
          /\ WF_vars(VoteP(p))
          /\ WF_vars(Receive(p))
          /\ WF_vars(UnilateralAbort(p))
          /\ WF_vars(CoordSend(p))
          /\ \A q \in Participants : WF_vars(Forward(p, q))

SpecNB == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

Agreement ==
    \A p, q \in Participants :
        (partAlive[p] /\ partAlive[q] /\ decision[p] # "none" /\ decision[q] # "none")
            => decision[p] = decision[q]

Validity ==
    /\ (\E p \in Participants : vote[p] = "no")
          => \A q \in Participants : partAlive[q] => decision[q] # "commit"
    /\ (coordAlive /\ \A p \in Participants : vote[p] = "yes")
          => \A q \in Participants : partAlive[q] => decision[q] # "abort"

(* Liveness *)

AllCommit ==
    ((<>[](\A p \in Participants : vote[p] = "yes")) /\ []coordAlive)
        => <>[](\A p \in Participants : partAlive[p] => decision[p] = "commit")

AllAbort ==
    (<>(\E p \in Participants : vote[p] = "no"))
        => <>[](\A p \in Participants : partAlive[p] => decision[p] = "abort")

Termination ==
    <>[](\A p \in Participants : partAlive[p] => decision[p] # "none")

=============================================================================
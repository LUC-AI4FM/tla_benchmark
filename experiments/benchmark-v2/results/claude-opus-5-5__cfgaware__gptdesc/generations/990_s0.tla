---------------------------- MODULE NBAC_RB ----------------------------
(***************************************************************************)
(* Non-blocking atomic commitment obtained via reliable broadcast.         *)
(* Base atomic-commitment part (voting, coordinator decision, coordinator  *)
(* crash) plus participant forwarding state: on receipt of a decision a    *)
(* participant forwards it to all other participants before delivering     *)
(* (deciding) it locally.                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT participants

VARIABLES
    pState,       \* participant state
    vote,         \* participant vote
    cState,       \* coordinator state: "init", "commit", "abort"
    cAlive,       \* coordinator alive?
    msgs,         \* set of messages sent
    preDecision,  \* decision received but not yet delivered
    forwarded     \* set of participants the decision was forwarded to

vars == <<pState, vote, cState, cAlive, msgs, preDecision, forwarded>>

Decisions == {"commit", "abort"}

Messages ==
    [type : {"decision"}, dec : Decisions]
    \cup [type : {"fwd"}, to : participants, dec : Decisions]

TypeOK ==
    /\ pState \in [participants -> {"working", "prepared", "commit", "abort"}]
    /\ vote \in [participants -> {"none", "yes", "no"}]
    /\ cState \in {"init", "commit", "abort"}
    /\ cAlive \in BOOLEAN
    /\ msgs \subseteq Messages
    /\ preDecision \in [participants -> {"none"} \cup Decisions]
    /\ forwarded \in [participants -> SUBSET participants]

Init ==
    /\ pState = [p \in participants |-> "working"]
    /\ vote = [p \in participants |-> "none"]
    /\ cState = "init"
    /\ cAlive = TRUE
    /\ msgs = {}
    /\ preDecision = [p \in participants |-> "none"]
    /\ forwarded = [p \in participants |-> {}]

(*************************** Base actions **********************************)

VoteYes(p) ==
    /\ pState[p] = "working"
    /\ vote' = [vote EXCEPT ![p] = "yes"]
    /\ pState' = [pState EXCEPT ![p] = "prepared"]
    /\ UNCHANGED <<cState, cAlive, msgs, preDecision, forwarded>>

VoteNo(p) ==
    /\ pState[p] = "working"
    /\ vote' = [vote EXCEPT ![p] = "no"]
    /\ pState' = [pState EXCEPT ![p] = "abort"]
    /\ UNCHANGED <<cState, cAlive, msgs, preDecision, forwarded>>

CoordCommit ==
    /\ cAlive
    /\ cState = "init"
    /\ \A p \in participants : vote[p] = "yes"
    /\ cState' = "commit"
    /\ msgs' = msgs \cup {[type |-> "decision", dec |-> "commit"]}
    /\ UNCHANGED <<pState, vote, cAlive, preDecision, forwarded>>

CoordAbort ==
    /\ cAlive
    /\ cState = "init"
    /\ \E p \in participants : vote[p] = "no"
    /\ cState' = "abort"
    /\ msgs' = msgs \cup {[type |-> "decision", dec |-> "abort"]}
    /\ UNCHANGED <<pState, vote, cAlive, preDecision, forwarded>>

CoordCrash ==
    /\ cAlive
    /\ cAlive' = FALSE
    /\ UNCHANGED <<pState, vote, cState, msgs, preDecision, forwarded>>

(********************** Participant-side NB actions ************************)

\* Pre-decide upon receiving the coordinator's decision
PreDecideCoord(p) ==
    /\ pState[p] = "prepared"
    /\ preDecision[p] = "none"
    /\ \E d \in Decisions :
         /\ [type |-> "decision", dec |-> d] \in msgs
         /\ preDecision' = [preDecision EXCEPT ![p] = d]
    /\ UNCHANGED <<pState, vote, cState, cAlive, msgs, forwarded>>

\* Pre-decide upon receiving a forwarded decision from another participant
PreDecideFwd(p) ==
    /\ pState[p] = "prepared"
    /\ preDecision[p] = "none"
    /\ \E d \in Decisions :
         /\ [type |-> "fwd", to |-> p, dec |-> d] \in msgs
         /\ preDecision' = [preDecision EXCEPT ![p] = d]
    /\ UNCHANGED <<pState, vote, cState, cAlive, msgs, forwarded>>

\* Forward the pre-decision to another participant
Forward(p, q) ==
    /\ q # p
    /\ preDecision[p] # "none"
    /\ q \notin forwarded[p]
    /\ msgs' = msgs \cup {[type |-> "fwd", to |-> q, dec |-> preDecision[p]]}
    /\ forwarded' = [forwarded EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED <<pState, vote, cState, cAlive, preDecision>>

\* Deliver the decision locally once forwarding is complete
Decide(p) ==
    /\ pState[p] = "prepared"
    /\ preDecision[p] # "none"
    /\ forwarded[p] = participants \ {p}
    /\ pState' = [pState EXCEPT ![p] = preDecision[p]]
    /\ UNCHANGED <<vote, cState, cAlive, msgs, preDecision, forwarded>>

\* Simulated timeout: coordinator crashed before deciding, nothing received
TimeoutAbort(p) ==
    /\ pState[p] = "prepared"
    /\ preDecision[p] = "none"
    /\ ~cAlive
    /\ cState = "init"
    /\ ~\E d \in Decisions : [type |-> "fwd", to |-> p, dec |-> d] \in msgs
    /\ preDecision' = [preDecision EXCEPT ![p] = "abort"]
    /\ UNCHANGED <<pState, vote, cState, cAlive, msgs, forwarded>>

ParticipantNB(p) ==
    \/ PreDecideCoord(p)
    \/ PreDecideFwd(p)
    \/ \E q \in participants : Forward(p, q)
    \/ Decide(p)
    \/ TimeoutAbort(p)

NextNB ==
    \/ \E p \in participants : VoteYes(p) \/ VoteNo(p) \/ ParticipantNB(p)
    \/ CoordCommit
    \/ CoordAbort
    \/ CoordCrash

SpecNB ==
    /\ Init
    /\ [][NextNB]_vars
    /\ WF_vars(CoordCommit)
    /\ WF_vars(CoordAbort)
    /\ \A p \in participants :
         /\ WF_vars(PreDecideCoord(p))
         /\ WF_vars(PreDecideFwd(p))
         /\ WF_vars(\E q \in participants : Forward(p, q))
         /\ WF_vars(Decide(p))
         /\ WF_vars(TimeoutAbort(p))

(****************************** Properties *********************************)

Agreement ==
    \A p, q \in participants :
        ~(pState[p] = "commit" /\ pState[q] = "abort")

\* Invalid liveness-style properties
AllCommit == <>(\A p \in participants : pState[p] = "commit")

AllAbort == <>(\A p \in participants : pState[p] = "abort")

AllYesVotesLeadToCommit ==
    (\A p \in participants : vote[p] = "yes")
        ~> (\A p \in participants : pState[p] = "commit")

=============================================================================
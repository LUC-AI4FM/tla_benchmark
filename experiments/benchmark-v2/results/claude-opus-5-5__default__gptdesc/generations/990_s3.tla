------------------------------ MODULE ACRB ------------------------------
(***************************************************************************)
(* Non-blocking atomic commitment using reliable broadcast.               *)
(* The base atomic-commitment model (coordinator, votes, failures) is      *)
(* included inline so the module is self-contained. On receiving a         *)
(* decision, a participant enters a pre-decided state, forwards the        *)
(* decision to every other participant, and only then decides locally.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Participant

ASSUME Participant # {}

VARIABLES coordinator, participant

vars == <<coordinator, participant>>

Votes       == {"yes", "no"}
CVotes      == {"none", "yes", "no"}
CDecisions  == {"none", "commit", "abort"}
PDecisions  == {"undecided", "precommit", "preabort", "commit", "abort"}
FwdMsgs     == {"notsent", "commit", "abort"}

-----------------------------------------------------------------------------
TypeOK ==
  /\ coordinator \in [ request   : [Participant -> BOOLEAN],
                       vote      : [Participant -> CVotes],
                       broadcast : [Participant -> BOOLEAN],
                       decision  : CDecisions,
                       alive     : BOOLEAN ]
  /\ participant \in [ Participant ->
                       [ vote     : Votes,
                         alive    : BOOLEAN,
                         voteSent : BOOLEAN,
                         decision : PDecisions,
                         forward  : [Participant -> FwdMsgs] ] ]

Init ==
  /\ coordinator = [ request   |-> [i \in Participant |-> FALSE],
                     vote      |-> [i \in Participant |-> "none"],
                     broadcast |-> [i \in Participant |-> FALSE],
                     decision  |-> "none",
                     alive     |-> TRUE ]
  /\ participant \in [ Participant ->
                       [ vote     : Votes,
                         alive    : {TRUE},
                         voteSent : {FALSE},
                         decision : {"undecided"},
                         forward  : {[j \in Participant |-> "notsent"]} ] ]

-----------------------------------------------------------------------------
(* Base coordinator actions *)

CoordSendReq(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "none"
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

CoordDecide ==
  /\ coordinator.alive
  /\ coordinator.decision = "none"
  /\ \/ /\ \A i \in Participant : coordinator.vote[i] = "yes"
        /\ coordinator' = [coordinator EXCEPT !.decision = "commit"]
     \/ /\ \E i \in Participant : coordinator.vote[i] = "no"
        /\ coordinator' = [coordinator EXCEPT !.decision = "abort"]
  /\ UNCHANGED participant

CoordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # "none"
  /\ ~coordinator.broadcast[i]
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
  /\ UNCHANGED participant

CoordFail ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

(* Base participant actions *)

ParSendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]

ParFail(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
(* Reliable-broadcast extension *)

PreDecided(i) == participant[i].decision \in {"precommit", "preabort"}

DecisionOf(i) == IF participant[i].decision = "precommit" THEN "commit" ELSE "abort"

(* Pre-decide on receiving the coordinator's broadcast *)
ParPreDecideOnCoord(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ coordinator.broadcast[i]
  /\ participant' = [participant EXCEPT ![i].decision =
                       IF coordinator.decision = "commit" THEN "precommit"
                                                          ELSE "preabort"]
  /\ UNCHANGED coordinator

(* Pre-decide on receiving a forwarded decision from another participant *)
ParPreDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ participant[j].forward[i] # "notsent"
  /\ participant' = [participant EXCEPT ![i].decision =
                       IF participant[j].forward[i] = "commit" THEN "precommit"
                                                               ELSE "preabort"]
  /\ UNCHANGED coordinator

(* Forward the pre-decision to participant j *)
ParForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ PreDecided(i)
  /\ participant[i].forward[j] = "notsent"
  /\ participant' = [participant EXCEPT ![i].forward[j] = DecisionOf(i)]
  /\ UNCHANGED coordinator

(* Decide locally once forwarding to all others is complete *)
ParDecide(i) ==
  /\ participant[i].alive
  /\ PreDecided(i)
  /\ \A j \in Participant \ {i} : participant[i].forward[j] # "notsent"
  /\ participant' = [participant EXCEPT ![i].decision = DecisionOf(i)]
  /\ UNCHANGED coordinator

(* Simulated timeout: coordinator crashed, nothing received, and no other  *)
(* live participant is in the middle of forwarding a decision.             *)
ParTimeoutAbort(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ ~coordinator.alive
  /\ ~coordinator.broadcast[i]
  /\ \A j \in Participant \ {i} :
        /\ participant[j].forward[i] = "notsent"
        /\ (participant[j].alive => participant[j].decision \in {"undecided", "abort"})
  /\ participant' = [participant EXCEPT ![i].decision = "preabort"]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
CoordProgress ==
  \/ \E i \in Participant : CoordSendReq(i) \/ CoordBroadcast(i)
  \/ CoordDecide

ParProgress(i) ==
  \/ ParSendVote(i)
  \/ ParPreDecideOnCoord(i)
  \/ \E j \in Participant : ParPreDecideOnForward(i, j) \/ ParForward(i, j)
  \/ ParDecide(i)
  \/ ParTimeoutAbort(i)

Next ==
  \/ CoordProgress
  \/ CoordFail
  \/ \E i \in Participant : ParProgress(i) \/ ParFail(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CoordProgress)
  /\ \A i \in Participant : WF_vars(ParProgress(i))

-----------------------------------------------------------------------------
(* Safety *)

AC1 ==  \* agreement
  \A i, j \in Participant :
     ~(participant[i].decision = "commit" /\ participant[j].decision = "abort")

AC2 ==  \* commit only if all voted yes
  (\E i \in Participant : participant[i].decision = "commit")
     => \A j \in Participant : participant[j].vote = "yes"

PreAgreement ==
  \A i, j \in Participant :
     ~(participant[i].decision \in {"precommit", "commit"}
       /\ participant[j].decision \in {"preabort", "abort"}
       /\ participant[j].alive /\ participant[i].alive)
     \/ ~participant[i].alive \/ ~participant[j].alive

Invariant == TypeOK /\ AC1 /\ AC2

(* Liveness: non-blocking termination *)
AC4 ==
  <>[](\A i \in Participant :
         participant[i].alive => participant[i].decision \in {"commit", "abort"})

(* Invalid liveness-style properties (expected to be violated) *)
AllCommit ==
  <>(\A i \in Participant : participant[i].decision = "commit")

AllAbort ==
  <>(\A i \in Participant : participant[i].decision = "abort")

AllYesLeadsToCommit ==
  (\A i \in Participant : participant[i].vote = "yes")
     ~> (\A i \in Participant : participant[i].decision = "commit")

THEOREM Spec => []Invariant
=============================================================================
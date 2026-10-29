-------------------------------- MODULE MC_ACP_SB --------------------------------
(***************************************************************************)
(* Apalache type annotations for the atomic commitment protocol ACP_SB.    *)
(* The original specification stays free of tool-specific annotations;     *)
(* this module supplies typed constants and variables for participants,    *)
(* participant state, coordinator state and the tag constants. It also     *)
(* gives a concrete set of participants for the configuration.             *)
(*                                                                         *)
(* The protocol definitions of ACP_SB are given inline below, so that this *)
(* module parses on its own.                                               *)
(***************************************************************************)

CONSTANTS
    \* @type: Set(PARTICIPANT);
    participants,
    \* @type: VOTE;
    yes,
    \* @type: VOTE;
    no,
    \* @type: DECISION;
    undecided,
    \* @type: DECISION;
    commit,
    \* @type: DECISION;
    abort,
    \* @type: VOTE;
    waiting,
    \* @type: DECISION;
    notsent

\* Concrete value for the participants, used by the configuration.
participantsVal == { "p1_OF_PARTICIPANT", "p2_OF_PARTICIPANT", "p3_OF_PARTICIPANT" }

VARIABLES
    \* @type: PARTICIPANT -> [vote: VOTE, alive: Bool, decision: DECISION, faulty: Bool, voteSent: Bool, forward: PARTICIPANT -> DECISION];
    participant,
    \* @type: [request: PARTICIPANT -> Bool, vote: PARTICIPANT -> VOTE, alive: Bool, decision: DECISION, broadcast: PARTICIPANT -> Bool];
    coordinator

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(* Type invariant                                                          *)
---------------------------------------------------------------------------

TypeInvParticipant ==
    participant \in [participants ->
                       [ vote     : {yes, no},
                         alive    : BOOLEAN,
                         decision : {undecided, commit, abort},
                         faulty   : BOOLEAN,
                         voteSent : BOOLEAN,
                         forward  : [participants -> {notsent, commit, abort}] ]]

TypeInvCoordinator ==
    coordinator \in [ request   : [participants -> BOOLEAN],
                      vote      : [participants -> {waiting, yes, no}],
                      alive     : BOOLEAN,
                      decision  : {undecided, commit, abort},
                      broadcast : [participants -> BOOLEAN] ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

---------------------------------------------------------------------------
(* Initial state                                                           *)
---------------------------------------------------------------------------

InitParticipant ==
    participant \in [participants ->
                       [ vote     : {yes, no},
                         alive    : {TRUE},
                         decision : {undecided},
                         faulty   : {FALSE},
                         voteSent : {FALSE},
                         forward  : {[k \in participants |-> notsent]} ]]

InitCoordinator ==
    coordinator = [ request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    alive     |-> TRUE,
                    decision  |-> undecided,
                    broadcast |-> [i \in participants |-> FALSE] ]

Init == InitParticipant /\ InitCoordinator

---------------------------------------------------------------------------
(* Coordinator actions                                                     *)
---------------------------------------------------------------------------

request(i) ==
    /\ coordinator.alive
    /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
    /\ UNCHANGED participant

getVote(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.vote[i] = waiting
    /\ participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
    /\ UNCHANGED participant

detectFault(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.vote[i] = waiting
    /\ ~participant[i].alive
    /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED participant

makeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.vote[j] # waiting
    /\ coordinator' = [coordinator EXCEPT !.decision =
                          IF \A j \in participants : coordinator.vote[j] = yes
                          THEN commit ELSE abort]
    /\ UNCHANGED participant

coordBroadcast(i) ==
    /\ coordinator.alive
    /\ coordinator.decision # undecided
    /\ ~coordinator.broadcast[i]
    /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
    /\ UNCHANGED participant

coordDie ==
    /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
    /\ UNCHANGED participant

---------------------------------------------------------------------------
(* Participant actions                                                     *)
---------------------------------------------------------------------------

sendVote(i) ==
    /\ participant[i].alive
    /\ coordinator.request[i]
    /\ ~participant[i].voteSent
    /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
    /\ UNCHANGED coordinator

abortOnVote(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[i].voteSent
    /\ participant[i].vote = no
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ ~coordinator.request[i]
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

decide(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ coordinator.broadcast[i]
    /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
    /\ UNCHANGED coordinator

forward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].decision # undecided
    /\ participant[i].forward[j] = notsent
    /\ participant' = [participant EXCEPT ![i].forward[j] = participant[i].decision]
    /\ UNCHANGED coordinator

decideOnForward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[j].forward[i] # notsent
    /\ participant' = [participant EXCEPT ![i].decision = participant[j].forward[i]]
    /\ UNCHANGED coordinator

parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relation                                                     *)
---------------------------------------------------------------------------

coordProgN ==
    \/ \E i \in participants : request(i) \/ getVote(i) \/ detectFault(i)
                               \/ coordBroadcast(i)
    \/ makeDecision

parProgN ==
    \E i \in participants :
        \/ sendVote(i)
        \/ abortOnVote(i)
        \/ abortOnTimeoutRequest(i)
        \/ decide(i)
        \/ \E j \in participants : forward(i, j) \/ decideOnForward(i, j)

failures ==
    \/ coordDie
    \/ \E i \in participants : parDie(i)

progN == coordProgN \/ parProgN \/ failures

Spec == Init /\ [][progN]_vars

=============================================================================
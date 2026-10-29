------------------------------ MODULE APAACP_SB ------------------------------
(***************************************************************************)
(* Apalache type annotations for ACP_SB (Atomic Commitment Protocol with   *)
(* Simple Broadcast).                                                      *)
(*                                                                         *)
(* The original wrapper declares typed constants and variables and then    *)
(* writes INSTANCE ACP_SB. That way the original ACP_SB specification      *)
(* stays free of tool-specific annotations. This module must pass SANY     *)
(* without ACP_SB.tla being present, so the instantiated ACP_SB definitions *)
(* are reproduced inline below. The typed interface is the same:           *)
(* participants, participant state, coordinator state, and the tag         *)
(* constants (yes, no, undecided, commit, abort, waiting).                 *)
(* ConstParticipants gives a concrete participant set for configuration.   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    participants,
    \* @type: Str;
    yes,
    \* @type: Str;
    no,
    \* @type: Str;
    undecided,
    \* @type: Str;
    commit,
    \* @type: Str;
    abort,
    \* @type: Str;
    waiting

VARIABLES
    \* @type: Str -> [vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool];
    participant,
    \* @type: [request: Str -> Bool, vote: Str -> Str, broadcast: Str -> Bool, decision: Str, alive: Bool];
    coordinator

vars == <<participant, coordinator>>

\* Concrete participant set used by the model-checking configuration
ConstParticipants == {"1_OF_PARTICIPANT", "2_OF_PARTICIPANT", "3_OF_PARTICIPANT"}

---------------------------------------------------------------------------
(*************************** Instantiated ACP_SB ***************************)

TypeInvParticipant ==
    participant \in [participants -> [vote     : {yes, no},
                                      alive    : BOOLEAN,
                                      decision : {undecided, commit, abort},
                                      faulty   : BOOLEAN,
                                      voteSent : BOOLEAN]]

TypeInvCoordinator ==
    coordinator \in [request   : [participants -> BOOLEAN],
                     vote      : [participants -> {waiting, yes, no}],
                     broadcast : [participants -> BOOLEAN],
                     decision  : {undecided, commit, abort},
                     alive     : BOOLEAN]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant ==
    participant \in [participants -> [vote     : {yes, no},
                                      alive    : {TRUE},
                                      decision : {undecided},
                                      faulty   : {FALSE},
                                      voteSent : {FALSE}]]

InitCoordinator ==
    coordinator = [request   |-> [i \in participants |-> FALSE],
                   vote      |-> [i \in participants |-> waiting],
                   broadcast |-> [i \in participants |-> FALSE],
                   decision  |-> undecided,
                   alive     |-> TRUE]

Init == InitParticipant /\ InitCoordinator

(* Coordinator actions *)

request(i) ==
    /\ coordinator.alive
    /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
    /\ UNCHANGED participant

getVote(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.request[j]
    /\ coordinator.vote[i] = waiting
    /\ participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
    /\ UNCHANGED participant

detectFault(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.request[j]
    /\ coordinator.vote[i] = waiting
    /\ ~participant[i].alive
    /\ ~participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
    /\ UNCHANGED participant

makeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
    /\ coordinator' = [coordinator EXCEPT !.decision =
                          IF \A j \in participants : coordinator.vote[j] = yes
                          THEN commit ELSE abort]
    /\ UNCHANGED participant

coordBroadcast(i) ==
    /\ coordinator.alive
    /\ coordinator.decision \in {commit, abort}
    /\ ~coordinator.broadcast[i]
    /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
    /\ UNCHANGED participant

coordDie ==
    /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
    /\ UNCHANGED participant

(* Participant actions *)

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

parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                          ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

CoordinatorStep ==
    \/ \E i \in participants :
          request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
    \/ makeDecision

ParticipantStep(i) ==
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ decide(i)

Next ==
    \/ CoordinatorStep
    \/ coordDie
    \/ \E i \in participants : ParticipantStep(i) \/ parDie(i)

Fairness ==
    /\ WF_vars(CoordinatorStep)
    /\ \A i \in participants : WF_vars(ParticipantStep(i))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Correctness properties of ACP_SB *)

\* AC1: no two participants reach different decisions
AC1 ==
    \A i, j \in participants :
        ~(participant[i].decision = commit /\ participant[j].decision = abort)

\* AC2: a participant commits only if all participants voted yes
AC2 ==
    (\E i \in participants : participant[i].decision = commit)
        => (\A j \in participants : participant[j].vote = yes)

\* AC3_1: if all vote yes and nobody fails, everyone eventually commits
AC3_1 ==
    ((\A i \in participants : participant[i].alive /\ participant[i].vote = yes)
        /\ coordinator.alive
        /\ [](coordinator.alive /\ \A i \in participants : participant[i].alive))
    ~> (\A i \in participants : participant[i].decision = commit)

\* AC4: decisions are irreversible
AC4 ==
    [][\A i \in participants :
         participant[i].decision \in {commit, abort}
            => participant'[i].decision = participant[i].decision]_vars

THEOREM Spec => [](TypeInv /\ AC1 /\ AC2) /\ AC4
=============================================================================
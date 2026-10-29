-------------------------- MODULE APA_ACP_SB --------------------------
(***************************************************************************)
(* Apalache-typed version of the atomic commitment protocol with simple   *)
(* broadcast (ACP_SB).                                                     *)
(*                                                                         *)
(* The original ACP_SB module stays free of tool-specific annotations.     *)
(* This module supplies the typing information that Apalache needs for    *)
(* participants, participant state, coordinator state and the tag         *)
(* constants (yes, no, undecided, commit, abort, waiting, notsent). It     *)
(* also gives a concrete participant set through ConstInit, which the      *)
(* configuration uses.                                                     *)
(*                                                                         *)
(* The protocol is written out inline below so that this module parses by  *)
(* itself. With ACP_SB.tla available, the inline part can be replaced by:  *)
(*     INSTANCE ACP_SB                                                     *)
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
    waiting,
    \* @type: Str;
    notsent

VARIABLES
    \* @type: Str -> { vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool, forward: Str -> Str };
    participant,
    \* @type: { request: Str -> Bool, vote: Str -> Str, broadcast: Str -> Str, decision: Str, alive: Bool, faulty: Bool };
    coordinator

vars == <<participant, coordinator>>

(***************************************************************************)
(* Concrete constant values used by the Apalache configuration.            *)
(***************************************************************************)
ConstInit ==
    /\ participants = {"p1", "p2", "p3"}
    /\ yes = "yes"
    /\ no = "no"
    /\ undecided = "undecided"
    /\ commit = "commit"
    /\ abort = "abort"
    /\ waiting = "waiting"
    /\ notsent = "notsent"

ASSUME Cardinality({yes, no, undecided, commit, abort, waiting, notsent}) = 7

(***************************************************************************)
(* Type invariants                                                          *)
(***************************************************************************)
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
                      broadcast : [participants -> {commit, abort, notsent}],
                      decision  : {commit, abort, undecided},
                      alive     : BOOLEAN,
                      faulty    : BOOLEAN ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

(***************************************************************************)
(* Initial state                                                            *)
(***************************************************************************)
InitParticipant ==
    participant \in [participants ->
                       [ vote     : {yes, no},
                         alive    : {TRUE},
                         decision : {undecided},
                         faulty   : {FALSE},
                         voteSent : {FALSE},
                         forward  : {[j \in participants |-> notsent]} ]]

InitCoordinator ==
    coordinator = [ request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    broadcast |-> [i \in participants |-> notsent],
                    decision  |-> undecided,
                    alive     |-> TRUE,
                    faulty    |-> FALSE ]

Init == InitParticipant /\ InitCoordinator

(***************************************************************************)
(* Coordinator actions                                                      *)
(***************************************************************************)
request(i) ==
    /\ coordinator.alive
    /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
    /\ UNCHANGED participant

getVote(i) ==
    /\ coordinator.alive
    /\ coordinator.vote[i] = waiting
    /\ participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
    /\ UNCHANGED participant

coordDecideCommit ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A i \in participants : coordinator.vote[i] = yes
    /\ coordinator' = [coordinator EXCEPT !.decision = commit]
    /\ UNCHANGED participant

coordDecideAbort ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \E i \in participants :
          \/ coordinator.vote[i] = no
          \/ (coordinator.vote[i] = waiting /\ ~participant[i].alive)
    /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED participant

coordBroadcast(i) ==
    /\ coordinator.alive
    /\ coordinator.decision # undecided
    /\ coordinator.broadcast[i] = notsent
    /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
    /\ UNCHANGED participant

coordFail ==
    /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
    /\ UNCHANGED participant

(***************************************************************************)
(* Participant actions                                                      *)
(***************************************************************************)
sendVote(i) ==
    /\ participant[i].alive
    /\ coordinator.request[i]
    /\ ~participant[i].voteSent
    /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
    /\ UNCHANGED coordinator

abortOnNo(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[i].vote = no
    /\ participant[i].voteSent
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

decideFromCoordinator(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ coordinator.broadcast[i] # notsent
    /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
    /\ UNCHANGED coordinator

forward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].decision # undecided
    /\ participant[i].forward[j] = notsent
    /\ participant' = [participant EXCEPT ![i].forward[j] = participant[i].decision]
    /\ UNCHANGED coordinator

decideFromForward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[j].forward[i] # notsent
    /\ participant' = [participant EXCEPT ![i].decision = participant[j].forward[i]]
    /\ UNCHANGED coordinator

participantFail(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

(***************************************************************************)
(* Next-state relation and specification                                    *)
(***************************************************************************)
CoordinatorProgress ==
    \/ \E i \in participants : request(i) \/ getVote(i) \/ coordBroadcast(i)
    \/ coordDecideCommit
    \/ coordDecideAbort

ParticipantProgress ==
    \E i \in participants :
        \/ sendVote(i)
        \/ abortOnNo(i)
        \/ decideFromCoordinator(i)
        \/ \E j \in participants : forward(i, j) \/ decideFromForward(i, j)

Failures ==
    \/ coordFail
    \/ \E i \in participants : participantFail(i)

Next == CoordinatorProgress \/ ParticipantProgress \/ Failures

Fairness ==
    /\ \A i \in participants :
          /\ WF_vars(request(i))
          /\ WF_vars(getVote(i))
          /\ WF_vars(coordBroadcast(i))
          /\ WF_vars(sendVote(i))
          /\ WF_vars(abortOnNo(i))
          /\ WF_vars(decideFromCoordinator(i))
          /\ \A j \in participants :
                /\ WF_vars(forward(i, j))
                /\ WF_vars(decideFromForward(i, j))
    /\ WF_vars(coordDecideCommit)
    /\ WF_vars(coordDecideAbort)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Correctness properties of atomic commitment                              *)
(***************************************************************************)
\* AC1: all participants that decide reach the same decision.
AC1 ==
    \A i, j \in participants :
        ~(participant[i].decision = commit /\ participant[j].decision = abort)

\* AC2: a commit happens only if every participant voted yes.
AC2 ==
    (\E i \in participants : participant[i].decision = commit)
        => (\A j \in participants : participant[j].vote = yes)

\* AC3: an abort happens only if some participant voted no or a failure occurred.
AC3 ==
    (\E i \in participants : participant[i].decision = abort)
        => \/ \E j \in participants : participant[j].vote = no
           \/ \E j \in participants : participant[j].faulty
           \/ coordinator.faulty

\* AC4: decisions are irreversible.
AC4 ==
    [][\A i \in participants :
          participant[i].decision # undecided
             => participant'[i].decision = participant[i].decision]_vars

\* AC5: if the coordinator never fails, every live participant eventually decides.
AC5 ==
    ([]coordinator.alive)
        => <>(\A i \in participants :
                 participant[i].alive => participant[i].decision # undecided)

Safety == TypeInv /\ AC1 /\ AC2 /\ AC3

THEOREM Spec => [](TypeInv /\ AC1 /\ AC2 /\ AC3)
THEOREM Spec => AC4
THEOREM Spec => AC5
=============================================================================
---------------------------- MODULE MC_ACP_NB ----------------------------
(***************************************************************************)
(* Non-blocking atomic commitment protocol (ACP_NB), self-contained and    *)
(* set up for model checking with TLC.                                     *)
(*                                                                         *)
(* TLC configuration (MC_ACP_NB.cfg):                                      *)
(*   CONSTANTS participants = {p0, p1}                                     *)
(*             yes = yes  no = no  undecided = undecided                   *)
(*             commit = commit  abort = abort                              *)
(*             waiting = waiting  notsent = notsent                        *)
(*   SPECIFICATION SpecNB                                                  *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(*   SYMMETRY Perms                                                        *)
(*   INVARIANTS TypeOK AC1 AC2 AC3_1                                       *)
(*   PROPERTIES AC4_alt AC3_2 AC5                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants,             \* set of participants
          yes, no,                  \* votes
          undecided, commit, abort, \* decisions
          waiting,                  \* coordinator waiting for a vote
          notsent                   \* no decision forwarded yet

VARIABLES participant,  \* participant[i] : state of participant i
          coordinator   \* state of the coordinator

vars == <<participant, coordinator>>

(* Symmetry set for TLC *)
Perms == Permutations(participants)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeInfoParticipant(p) ==
    p \in [ vote     : {yes, no},
            alive    : BOOLEAN,
            decision : {undecided, commit, abort},
            faulty   : BOOLEAN,
            voteSent : BOOLEAN,
            forward  : [participants -> {notsent, commit, abort}] ]

TypeInfoCoordinator(c) ==
    c \in [ request   : [participants -> BOOLEAN],
            vote      : [participants -> {waiting, yes, no}],
            broadcast : [participants -> BOOLEAN],
            decision  : {undecided, commit, abort},
            alive     : BOOLEAN,
            faulty    : BOOLEAN ]

TypeOK ==
    /\ \A i \in participants : TypeInfoParticipant(participant[i])
    /\ TypeInfoCoordinator(coordinator)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
InitParticipant ==
    participant \in [ participants ->
                        [ vote     : {yes, no},
                          alive    : {TRUE},
                          decision : {undecided},
                          faulty   : {FALSE},
                          voteSent : {FALSE},
                          forward  : {[j \in participants |-> notsent]} ] ]

InitCoordinator ==
    coordinator = [ request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    broadcast |-> [i \in participants |-> FALSE],
                    decision  |-> undecided,
                    alive     |-> TRUE,
                    faulty    |-> FALSE ]

Init == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)
request(i) ==
    /\ coordinator.alive
    /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
    /\ UNCHANGED participant

getVote(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.request[i]
    /\ coordinator.vote[i] = waiting
    /\ participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
    /\ UNCHANGED participant

detectFault(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.request[i]
    /\ coordinator.vote[i] = waiting
    /\ ~participant[i].alive
    /\ ~participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED participant

makeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
    /\ coordinator' =
         [coordinator EXCEPT !.decision =
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
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
    /\ UNCHANGED participant

-----------------------------------------------------------------------------
(***************************************************************************)
(* Participant actions                                                     *)
(* A participant that decides forwards its decision to all other           *)
(* participants in the same step (non-blocking extension).                 *)
(***************************************************************************)
DecideAndForward(i, d) ==
    participant' = [participant EXCEPT
                       ![i].decision = d,
                       ![i].forward  = [j \in participants |->
                                           IF j = i THEN notsent ELSE d]]

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
    /\ DecideAndForward(i, abort)
    /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ ~coordinator.request[i]
    /\ DecideAndForward(i, abort)
    /\ UNCHANGED coordinator

decide(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ coordinator.broadcast[i]
    /\ DecideAndForward(i, coordinator.decision)
    /\ UNCHANGED coordinator

decideOnForward(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ \E j \in participants :
          /\ participant[j].forward[i] # notsent
          /\ DecideAndForward(i, participant[j].forward[i])
    /\ UNCHANGED coordinator

(* Coordinator has failed, no decision was forwarded to i and no alive    *)
(* participant still has a pending broadcast from the coordinator.        *)
abortOnTimeout(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ \A j \in participants :
          /\ participant[j].forward[i] = notsent
          /\ participant[j].alive => ~coordinator.broadcast[j]
    /\ DecideAndForward(i, abort)
    /\ UNCHANGED coordinator

parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                          ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
CoordProg ==
    \/ \E i \in participants :
          request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
    \/ makeDecision

ParProg(i) ==
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ decide(i)
    \/ decideOnForward(i)
    \/ abortOnTimeout(i)

Next ==
    \/ CoordProg
    \/ coordDie
    \/ \E i \in participants : ParProg(i) \/ parDie(i)

Fairness ==
    /\ WF_vars(makeDecision)
    /\ \A i \in participants :
          /\ WF_vars(request(i))
          /\ WF_vars(getVote(i))
          /\ WF_vars(detectFault(i))
          /\ WF_vars(coordBroadcast(i))
          /\ WF_vars(ParProg(i))

SpecNB == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)
AllYes     == \A i \in participants : participant[i].vote = yes
NoFailures == /\ ~coordinator.faulty
              /\ \A i \in participants : ~participant[i].faulty

(* AC1: all participants that decide reach the same decision *)
AC1 == \A i, j \in participants :
          ~(participant[i].decision = commit /\ participant[j].decision = abort)

(* AC2: commit only if all participants voted yes *)
AC2 == \A i \in participants :
          participant[i].decision = commit => AllYes

(* AC3_1: abort only if some participant voted no or a failure occurred *)
AC3_1 == \A i \in participants :
          participant[i].decision = abort =>
             (\E j \in participants : participant[j].vote = no) \/ ~NoFailures

(* AC3_2: if all vote yes and no failures ever occur, everyone commits *)
AC3_2 == (AllYes /\ []NoFailures) =>
            <>(\A i \in participants : participant[i].decision = commit)

(* AC4: decisions are stable (original temporal formulation) *)
AC4 == \A i \in participants :
          /\ [](participant[i].decision = commit =>
                   [](participant[i].decision = commit))
          /\ [](participant[i].decision = abort =>
                   [](participant[i].decision = abort))

(* AC4_alt: action-level formulation, more efficient for TLC *)
AC4_alt == [][\A i \in participants :
                 /\ participant[i].decision = commit =>
                       participant'[i].decision = commit
                 /\ participant[i].decision = abort =>
                       participant'[i].decision = abort]_vars

(* AC5: non-blocking -- every alive participant eventually decides *)
AC5 == <>(\A i \in participants :
             participant[i].alive => participant[i].decision # undecided)

=============================================================================
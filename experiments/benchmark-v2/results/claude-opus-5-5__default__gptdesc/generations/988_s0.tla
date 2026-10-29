------------------------------ MODULE ACP_NB_TLC ------------------------------
EXTENDS Naturals, TLC

--------------------------------- MODULE ACP_NB --------------------------------
CONSTANTS participants, yes, no, undecided, commit, abort, waiting, notsent

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

TypeInvParticipant ==
    participant \in [participants ->
        [ vote     : {yes, no},
          alive    : BOOLEAN,
          decision : {undecided, commit, abort},
          faulty   : BOOLEAN,
          voteSent : BOOLEAN,
          forward  : [participants -> {notsent, commit, abort}] ]]

TypeInvCoordinator ==
    coordinator \in
        [ request   : [participants -> BOOLEAN],
          vote      : [participants -> {waiting, yes, no}],
          alive     : BOOLEAN,
          decision  : {undecided, commit, abort},
          broadcast : [participants -> BOOLEAN] ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

InitParticipant ==
    participant \in [participants ->
        [ vote     : {yes, no},
          alive    : {TRUE},
          decision : {undecided},
          faulty   : {FALSE},
          voteSent : {FALSE},
          forward  : [participants -> {notsent}] ]]

InitCoordinator ==
    coordinator \in
        [ request   : [participants -> {FALSE}],
          vote      : [participants -> {waiting}],
          alive     : {TRUE},
          decision  : {undecided},
          broadcast : [participants -> {FALSE}] ]

Init == InitParticipant /\ InitCoordinator

(* ---------------- Coordinator actions ---------------- *)
request(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
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
    /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED participant

makeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
          /\ coordinator' = [coordinator EXCEPT !.decision = commit]
       \/ /\ \E j \in participants : coordinator.vote[j] = no
          /\ coordinator' = [coordinator EXCEPT !.decision = abort]
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

(* ---------------- Participant actions ---------------- *)
sendVote(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~participant[i].voteSent
    /\ coordinator.request[i]
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

abortOnTimeout(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[i].voteSent
    /\ ~coordinator.alive
    /\ ~coordinator.broadcast[i]
    /\ \A j \in participants :
          /\ participant[j].alive => participant[j].decision = undecided
          /\ participant[j].forward[i] = notsent
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

(* ---------------- Composition ---------------- *)
coordProgress ==
    \/ \E i \in participants : request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
    \/ makeDecision

parProgress(i) ==
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ decide(i)
    \/ abortOnTimeout(i)
    \/ \E j \in participants : forward(i, j) \/ decideOnForward(i, j)

Next ==
    \/ coordProgress
    \/ coordDie
    \/ \E i \in participants : parProgress(i) \/ parDie(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(coordProgress)
    /\ \A i \in participants : WF_vars(parProgress(i))

(* ---------------- Properties ---------------- *)
AC1 == [](\A i, j \in participants :
             ~(participant[i].decision = commit /\ participant[j].decision = abort))

AC2 == [](\A i \in participants : participant[i].decision = commit =>
             \A j \in participants : participant[j].vote = yes)

AC3_1 == [](\A i \in participants : participant[i].decision = abort =>
             \/ \E j \in participants : participant[j].vote = no
             \/ \E j \in participants : participant[j].faulty
             \/ ~coordinator.alive)

AC4 == [][\A i \in participants : participant[i].decision # undecided =>
             participant'[i].decision = participant[i].decision]_<<participant>>

AC5 == <>(\A i \in participants : participant[i].alive => participant[i].decision # undecided)
================================================================================
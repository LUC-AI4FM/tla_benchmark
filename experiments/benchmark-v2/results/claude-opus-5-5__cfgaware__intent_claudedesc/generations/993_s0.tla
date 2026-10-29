---------------------------- MODULE ACP_SB ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  participants,
  yes, no,
  undecided, commit, abort,
  waiting,
  notsent

participantsVal == {"p1", "p2", "p3"}

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

-----------------------------------------------------------------------------
TypeInv ==
  /\ participant \in [participants ->
        [ vote     : {yes, no},
          alive    : BOOLEAN,
          decision : {undecided, commit, abort},
          faulty   : BOOLEAN,
          voteSent : BOOLEAN ]]
  /\ coordinator \in
        [ request   : [participants -> BOOLEAN],
          vote      : [participants -> {waiting, yes, no}],
          alive     : BOOLEAN,
          decision  : {undecided, commit, abort},
          broadcast : [participants -> {commit, abort, notsent}] ]

-----------------------------------------------------------------------------
Init ==
  /\ participant \in [participants ->
        [ vote     : {yes, no},
          alive    : {TRUE},
          decision : {undecided},
          faulty   : {FALSE},
          voteSent : {FALSE} ]]
  /\ coordinator =
        [ request   |-> [i \in participants |-> FALSE],
          vote      |-> [i \in participants |-> waiting],
          alive     |-> TRUE,
          decision  |-> undecided,
          broadcast |-> [i \in participants |-> notsent] ]

-----------------------------------------------------------------------------
(* Coordinator actions *)

request(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
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
  /\ \A j \in participants : coordinator.vote[j] # waiting
  /\ coordinator' = [coordinator EXCEPT !.decision =
                        IF \A j \in participants : coordinator.vote[j] = yes
                        THEN commit ELSE abort]
  /\ UNCHANGED participant

coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

-----------------------------------------------------------------------------
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
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ decide(i)

coordProg ==
  \/ \E i \in participants : request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
  \/ makeDecision

progN ==
  \/ coordProg
  \/ \E i \in participants : parProg(i)

fault ==
  \/ coordDie
  \/ \E i \in participants : parDie(i)

Next == progN \/ fault

Spec == Init /\ [][Next]_vars /\ WF_vars(progN)

-----------------------------------------------------------------------------
(* Correctness properties *)

AC1 == \A i, j \in participants :
         \/ participant[i].decision # commit
         \/ participant[j].decision # abort

AC2 == [] ( (\A i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes) )

AC3_1 == [] ( (\A i \in participants : participant[i].vote = yes /\ participant[i].alive)
              /\ coordinator.alive
              /\ (\A i \in participants : participant[i].decision # undecided)
              => (\A i \in participants : participant[i].decision = commit) )

AC3_2 == [] ( (\E i \in participants : participant[i].vote = no)
              => (\A j \in participants : participant[j].decision # commit) )

AC4 == \A i \in participants :
         /\ [][participant[i].decision = commit => participant'[i].decision = commit]_vars
         /\ [][participant[i].decision = abort  => participant'[i].decision = abort]_vars

AC5 == <> (\A i \in participants :
              participant[i].alive => participant[i].decision # undecided)

=============================================================================
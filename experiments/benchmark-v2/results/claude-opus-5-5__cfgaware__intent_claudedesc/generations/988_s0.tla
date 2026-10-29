------------------------------- MODULE ACP_NB -------------------------------
EXTENDS TLC

CONSTANTS
  participants,              \* set of participants
  yes, no,                   \* votes
  undecided, commit, abort,  \* decisions
  waiting,                   \* coordinator state wrt participant vote
  notsent                    \* broadcast / forward state

VARIABLES
  participant,   \* participant states
  coordinator    \* coordinator state

vars == <<participant, coordinator>>

-----------------------------------------------------------------------------
TypeInfo ==
  /\ participant \in [participants -> [vote     : {yes, no},
                                       alive    : BOOLEAN,
                                       decision : {undecided, commit, abort},
                                       faulty   : BOOLEAN,
                                       voteSent : BOOLEAN,
                                       forward  : [participants -> {notsent, commit, abort}]]]
  /\ coordinator \in [request   : [participants -> BOOLEAN],
                      vote      : [participants -> {waiting, yes, no}],
                      broadcast : [participants -> {commit, abort, notsent}],
                      decision  : {commit, abort, undecided},
                      alive     : BOOLEAN,
                      faulty    : BOOLEAN]

-----------------------------------------------------------------------------
InitParticipant ==
  participant \in [participants -> [vote     : {yes, no},
                                    alive    : {TRUE},
                                    decision : {undecided},
                                    faulty   : {FALSE},
                                    voteSent : {FALSE},
                                    forward  : [participants -> {notsent}]]]

InitCoordinator ==
  coordinator = [request   |-> [i \in participants |-> FALSE],
                 vote      |-> [i \in participants |-> waiting],
                 broadcast |-> [i \in participants |-> notsent],
                 decision  |-> undecided,
                 alive     |-> TRUE,
                 faulty    |-> FALSE]

Init == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
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

\* Reliable broadcast: the decision reaches all participants atomically
coordBroadcast ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ \A j \in participants : coordinator.broadcast[j] = notsent
  /\ coordinator' = [coordinator EXCEPT
                       !.broadcast = [j \in participants |-> coordinator.decision]]
  /\ UNCHANGED participant

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
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

\* Non-blocking extension: decided participants forward their decision
forward(i, j) ==
  /\ participant[i].alive
  /\ participant[i].decision # undecided
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i].forward[j] = participant[i].decision]
  /\ UNCHANGED coordinator

decideOnForward(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ \E j \in participants :
        /\ participant[j].forward[i] # notsent
        /\ participant' = [participant EXCEPT ![i].decision = participant[j].forward[i]]
  /\ UNCHANGED coordinator

\* Coordinator failed without broadcasting any decision: safe to abort
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : coordinator.broadcast[j] = notsent
  /\ \A j \in participants : participant[j].forward[i] = notsent
  /\ participant' = [participant EXCEPT ![i].decision = abort]
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
  \/ decideOnForward(i)
  \/ abortOnTimeout(i)
  \/ \E j \in participants : forward(i, j)

parProgNB == \E i \in participants : parDie(i) \/ parProg(i)

coordProgB(i) == request(i) \/ getVote(i) \/ detectFault(i)

coordProgNB ==
  \/ coordDie
  \/ makeDecision
  \/ coordBroadcast
  \/ \E i \in participants : coordProgB(i)

progNB == parProgNB \/ coordProgNB

fairnessNB ==
  /\ \A i \in participants : WF_vars(parProg(i))
  /\ \A i \in participants : WF_vars(coordProgB(i))
  /\ WF_vars(makeDecision)
  /\ WF_vars(coordBroadcast)

SpecNB == Init /\ [][progNB]_vars /\ fairnessNB

-----------------------------------------------------------------------------
(* Correctness properties *)

\* Agreement: no two participants decide differently
AC1 == [] \A i, j \in participants :
            ~(participant[i].decision = commit /\ participant[j].decision = abort)

\* Commit only if all voted yes
AC2 == [] ((\E i \in participants : participant[i].decision = commit)
             => (\A j \in participants : participant[j].vote = yes))

\* Abort only if someone voted no or some failure occurred
AC3_1 == [] ((\E i \in participants : participant[i].decision = abort)
               => \/ \E j \in participants : participant[j].vote = no
                  \/ \E j \in participants : participant[j].faulty
                  \/ coordinator.faulty)

\* If all vote yes and no failures, eventually commit
AC3_2 == <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
            \/ \E j \in participants : participant[j].faulty
            \/ coordinator.faulty

\* Irrevocability of decisions
AC4_alt == [][\A i \in participants :
                /\ (participant[i].decision = commit => participant'[i].decision = commit)
                /\ (participant[i].decision = abort  => participant'[i].decision = abort)]_vars

\* Termination: every non-faulty participant eventually decides
AC5 == <> \A i \in participants :
            \/ participant[i].decision \in {abort, commit}
            \/ participant[i].faulty

\* Symmetry set for model checking
Perms == Permutations(participants)
=============================================================================
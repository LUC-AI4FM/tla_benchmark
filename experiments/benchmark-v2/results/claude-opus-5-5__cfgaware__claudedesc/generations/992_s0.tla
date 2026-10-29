------------------------------- MODULE ACP_SB -------------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).              *)
(***************************************************************************)

CONSTANTS participants   \* set of participants

yes       == "yes"
no        == "no"
undecided == "undecided"
commit    == "commit"
abort     == "abort"
waiting   == "waiting"
notsent   == "notsent"

VARIABLES
  participant,   \* function: participant -> participant state
  coordinator    \* coordinator record

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
TypeInvParticipant ==
  participant \in [participants -> [vote     : {yes, no},
                                    alive    : BOOLEAN,
                                    decision : {undecided, commit, abort},
                                    faulty   : BOOLEAN,
                                    voteSent : BOOLEAN]]

TypeInvCoordinator ==
  coordinator \in [request   : [participants -> BOOLEAN],
                   vote      : [participants -> {waiting, yes, no}],
                   broadcast : [participants -> {commit, abort, notsent}],
                   decision  : {commit, abort, undecided},
                   alive     : BOOLEAN,
                   faulty    : BOOLEAN]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

---------------------------------------------------------------------------
InitParticipant ==
  participant \in [participants -> [vote     : {yes, no},
                                    alive    : {TRUE},
                                    decision : {undecided},
                                    faulty   : {FALSE},
                                    voteSent : {FALSE}]]

InitCoordinator ==
  coordinator = [request   |-> [i \in participants |-> FALSE],
                 vote      |-> [i \in participants |-> waiting],
                 broadcast |-> [i \in participants |-> notsent],
                 decision  |-> undecided,
                 alive     |-> TRUE,
                 faulty    |-> FALSE]

Init == InitParticipant /\ InitCoordinator

---------------------------------------------------------------------------
(* Coordinator actions *)

request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.vote[i] = waiting
  /\ \A j \in participants : coordinator.request[j]
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.vote[i] = waiting
  /\ \A j \in participants : coordinator.request[j]
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
  /\ UNCHANGED participant

makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision \in {commit, abort}
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

---------------------------------------------------------------------------
(* Participant actions *)

sendVote(i) ==
  /\ participant[i].alive
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
  /\ coordinator.broadcast[i] \in {commit, abort}
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
Coordinator ==
  \/ makeDecision
  \/ coordDie
  \/ \E i \in participants :
       \/ request(i)
       \/ getVote(i)
       \/ detectFault(i)
       \/ coordBroadcast(i)

Participant ==
  \E i \in participants :
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ decide(i)
    \/ parDie(i)

Next == Coordinator \/ Participant

Fairness ==
  /\ WF_vars(makeDecision)
  /\ \A i \in participants :
       /\ WF_vars(request(i))
       /\ WF_vars(getVote(i))
       /\ WF_vars(detectFault(i))
       /\ WF_vars(coordBroadcast(i))
       /\ WF_vars(sendVote(i))
       /\ WF_vars(abortOnVote(i))
       /\ WF_vars(abortOnTimeoutRequest(i))
       /\ WF_vars(decide(i))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Properties *)

SomeFault ==
  \/ coordinator.faulty
  \/ \E j \in participants : participant[j].faulty

AC1 ==
  [] \A i, j \in participants :
       ~ (participant[i].decision = commit /\ participant[j].decision = abort)

AC2 ==
  [] ((\E i \in participants : participant[i].decision = commit)
        => (\A j \in participants : participant[j].vote = yes))

AC3_1 ==
  [] ((\E i \in participants : participant[i].decision = abort)
        => \/ \E j \in participants : participant[j].vote = no
           \/ SomeFault)

AC4 ==
  \A i \in participants :
    /\ [](participant[i].decision = commit => [](participant[i].decision = commit))
    /\ [](participant[i].decision = abort  => [](participant[i].decision = abort))

AC3_2 ==
  <> \/ \A i \in participants : participant[i].decision \in {abort, commit}
     \/ SomeFault

\* AC5 does NOT hold for simple broadcast: the coordinator may fail in the
\* middle of broadcasting, leaving live participants blocked forever.
AC5 ==
  <> \A i \in participants :
       \/ participant[i].decision \in {abort, commit}
       \/ participant[i].faulty

FaultyStable ==
  /\ \A i \in participants :
       [](participant[i].faulty => [](participant[i].faulty))
  /\ [](coordinator.faulty => [](coordinator.faulty))

VoteStable ==
  \A i \in participants :
    \/ [](participant[i].vote = yes)
    \/ [](participant[i].vote = no)

NoRecovery ==
  [] /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty
     /\ coordinator.alive <=> ~coordinator.faulty

StrongerAC2 ==
  [] ((\E i \in participants : participant[i].decision = commit)
        => /\ \A j \in participants : participant[j].vote = yes
           /\ coordinator.decision = commit)

StrongerAC3_1 ==
  [] ((\E i \in participants : participant[i].decision = abort)
        => \/ \E j \in participants :
                 participant[j].vote = no /\ participant[j].voteSent
           \/ \E j \in participants : participant[j].faulty
           \/ coordinator.faulty
           \/ coordinator.decision = abort)

AbortImpliesNoVote ==
  [] ((~SomeFault /\ \E i \in participants : participant[i].decision = abort)
        => \E j \in participants : participant[j].vote = no)

DecisionReachedNoFault ==
  ([] ~SomeFault)
    => <>(\A i \in participants : participant[i].decision \in {commit, abort})

=============================================================================
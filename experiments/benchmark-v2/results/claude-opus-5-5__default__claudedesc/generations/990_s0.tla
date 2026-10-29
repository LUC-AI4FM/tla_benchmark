------------------------------ MODULE ACP_NB ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS participants

ASSUME participants # {}

yes       == "yes"
no        == "no"
undecided == "undecided"
commit    == "commit"
abort     == "abort"
waiting   == "waiting"
notsent   == "notsent"

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

-----------------------------------------------------------------------------
TypeInvParticipant ==
  participant \in [participants ->
                    [ vote      : {yes, no},
                      alive     : BOOLEAN,
                      decision  : {undecided, commit, abort},
                      faulty    : BOOLEAN,
                      voteSent  : BOOLEAN,
                      forward   : [participants -> {notsent, commit, abort}] ]]

TypeInvCoordinator ==
  coordinator \in [ request   : [participants -> BOOLEAN],
                    vote      : [participants -> {waiting, yes, no}],
                    broadcast : [participants -> {commit, abort, notsent}],
                    decision  : {commit, abort, undecided},
                    alive     : BOOLEAN,
                    faulty    : BOOLEAN ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

-----------------------------------------------------------------------------
InitParticipant ==
  participant \in [participants ->
                    [ vote      : {yes, no},
                      alive     : {TRUE},
                      decision  : {undecided},
                      faulty    : {FALSE},
                      voteSent  : {FALSE},
                      forward   : {[k \in participants |-> notsent]} ]]

InitCoordinator ==
  coordinator = [ request   |-> [i \in participants |-> FALSE],
                  vote      |-> [i \in participants |-> waiting],
                  broadcast |-> [i \in participants |-> notsent],
                  decision  |-> undecided,
                  alive     |-> TRUE,
                  faulty    |-> FALSE ]

Init == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
(* Coordinator actions                                                      *)

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
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
  /\ UNCHANGED participant

makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A i \in participants : coordinator.vote[i] \in {yes, no}
  /\ \/ /\ \A i \in participants : coordinator.vote[i] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E i \in participants : coordinator.vote[i] = no
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

-----------------------------------------------------------------------------
(* Participant actions                                                      *)

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
  /\ participant[i].forward[i] = notsent
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant[i].forward[i] = notsent
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

(* Coordinator died before broadcasting to any alive participant, and no   *)
(* alive participant has received or been forwarded a pre-decision.        *)
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants :
        participant[j].alive =>
          /\ coordinator.broadcast[j] = notsent
          /\ \A k \in participants : participant[k].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

(* Receive pre-decision from the coordinator: store it in own slot.        *)
preDecideOnCoord(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT
                       ![i].forward[i] = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

(* Receive pre-decision forwarded by another participant j.                *)
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT
                       ![i].forward[i] = participant[j].forward[i]]
  /\ UNCHANGED coordinator

(* Forward own pre-decision to participant j.                              *)
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT
                       ![i].forward[j] = participant[i].forward[i]]
  /\ UNCHANGED coordinator

(* Decide only after forwarding to all participants.                       *)
decideNB(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].forward[i] # notsent
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT
                       ![i].decision = participant[i].forward[i]]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                        ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ abortOnTimeout(i)
  \/ preDecideOnCoord(i)
  \/ \E j \in participants : preDecideOnForward(i, j)
  \/ \E j \in participants : forward(i, j)
  \/ decideNB(i)

parProgNB ==
  \E i \in participants : parProg(i)

coordProg ==
  \/ \E i \in participants : request(i)
  \/ \E i \in participants : getVote(i)
  \/ \E i \in participants : detectFault(i)
  \/ makeDecision
  \/ \E i \in participants : coordBroadcast(i)

fail ==
  \/ coordDie
  \/ \E i \in participants : parDie(i)

Next == parProgNB \/ coordProg \/ fail

Fairness ==
  /\ \A i \in participants : WF_vars(parProg(i))
  /\ WF_vars(coordProg)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties                                                        *)

AC1 ==
  \A i, j \in participants :
     (participant[i].decision # undecided /\ participant[j].decision # undecided)
        => participant[i].decision = participant[j].decision

AC2 ==
  \A i \in participants :
     participant[i].decision = commit =>
        \A j \in participants : participant[j].vote = yes

AC3_1 ==
  \A i \in participants :
     participant[i].decision = commit => coordinator.decision = commit

AC3_2 ==
  (\A j \in participants : participant[j].vote = yes /\ ~participant[j].faulty)
  /\ ~coordinator.faulty
     => \A i \in participants : participant[i].decision # abort

(* Liveness: every alive participant eventually decides (non-blocking)      *)
AC4 ==
  <>[](\A i \in participants :
          participant[i].alive => participant[i].decision # undecided)

(* Liveness properties expected to be INVALID                              *)
AllCommit ==
  <>(\A i \in participants : participant[i].decision = commit)

AllAbort ==
  <>(\A i \in participants : participant[i].decision = abort)

AllCommitYesVotes ==
  (\A i \in participants : participant[i].vote = yes)
     ~> (\A i \in participants : participant[i].decision = commit)

THEOREM Spec => []TypeInv
=============================================================================
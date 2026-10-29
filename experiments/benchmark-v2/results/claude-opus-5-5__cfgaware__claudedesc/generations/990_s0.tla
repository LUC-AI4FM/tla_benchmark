------------------------------- MODULE ACP_NB -------------------------------
(***************************************************************************)
(* Non-Blocking Atomic Commitment Protocol (ACP-NB).                       *)
(* Extends the blocking protocol ACP_SB: a participant that receives a     *)
(* pre-decision (from the coordinator or another participant) first        *)
(* forwards it to all other participants and only then decides on it       *)
(* (reliable broadcast).                                                   *)
(***************************************************************************)

CONSTANTS
  participants,              \* set of participants
  yes, no,                   \* vote
  undecided, commit, abort,  \* decision
  waiting,                   \* coordinator state wrt a participant
  notsent                    \* broadcast state wrt a participant

VARIABLES
  participant,  \* participants (N)
  coordinator   \* coordinator  (1)

vars == <<participant, coordinator>>

(***************************************************************************)
(* Type invariants                                                         *)
(***************************************************************************)
TypeInvParticipant == participant \in [
                        participants -> [
                          vote     : {yes, no},
                          alive    : BOOLEAN,
                          decision : {undecided, commit, abort},
                          faulty   : BOOLEAN,
                          voteSent : BOOLEAN
                        ]
                      ]

TypeInvParticipantNB == participant \in [
                          participants -> [
                            vote     : {yes, no},
                            alive    : BOOLEAN,
                            decision : {undecided, commit, abort},
                            faulty   : BOOLEAN,
                            voteSent : BOOLEAN,
                            forward  : [participants -> {notsent, commit, abort}]
                          ]
                        ]

TypeInvCoordinator == coordinator \in [
                        request   : [participants -> BOOLEAN],
                        vote      : [participants -> {waiting, yes, no}],
                        alive     : BOOLEAN,
                        decision  : {undecided, commit, abort},
                        broadcast : [participants -> {commit, abort, notsent}]
                      ]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator
TypeInv   == TypeInvNB

(***************************************************************************)
(* Initial conditions                                                      *)
(***************************************************************************)
InitParticipantNB == participant \in [
                       participants -> [
                         vote     : {yes, no},
                         alive    : {TRUE},
                         decision : {undecided},
                         faulty   : {FALSE},
                         voteSent : {FALSE},
                         forward  : {[k \in participants |-> notsent]}
                       ]
                     ]

InitCoordinator == coordinator \in [
                     request   : {[k \in participants |-> FALSE]},
                     vote      : {[k \in participants |-> waiting]},
                     alive     : {TRUE},
                     decision  : {undecided},
                     broadcast : {[k \in participants |-> notsent]}
                   ]

InitNB == InitParticipantNB /\ InitCoordinator

(***************************************************************************)
(* Coordinator statements (as in ACP_SB)                                   *)
(***************************************************************************)
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
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
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

(***************************************************************************)
(* Participant statements                                                  *)
(***************************************************************************)
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

\* Coordinator died before broadcasting anything, and no alive participant
\* has received or forwarded a pre-decision.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ \A j \in participants : coordinator.broadcast[j] = notsent
  /\ \A j, k \in participants :
        participant[j].alive => participant[j].forward[k] = notsent
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Receive a pre-decision from the coordinator
preDecideOnCoord(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i].forward[i] = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

\* Receive a pre-decision forwarded by another participant
preDecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].forward[i] = notsent
  /\ participant[j].forward[i] # notsent
  /\ participant' = [participant EXCEPT ![i].forward[i] = participant[j].forward[i]]
  /\ UNCHANGED coordinator

preDecide(i) ==
  \/ preDecideOnCoord(i)
  \/ \E j \in participants : preDecideOnForward(i, j)

\* Forward the pre-decision to another participant
forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[i] # notsent
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i].forward[j] = participant[i].forward[i]]
  /\ UNCHANGED coordinator

\* Decide only once forwarding to everyone is complete
decideNB(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ \A j \in participants : participant[i].forward[j] # notsent
  /\ participant' = [participant EXCEPT ![i].decision = participant[i].forward[i]]
  /\ UNCHANGED coordinator

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
parProgNB(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ abortOnTimeout(i)
  \/ preDecide(i)
  \/ \E j \in participants : forward(i, j)
  \/ decideNB(i)

coordProg ==
  \/ \E i \in participants :
        request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
  \/ makeDecision

parProgNNB == \E i \in participants : parProgNB(i)

parFail == \E i \in participants : parDie(i)

coordFail == coordDie

NextNB ==
  \/ parProgNNB
  \/ coordProg
  \/ parFail
  \/ coordFail

fairness ==
  /\ \A i \in participants : WF_vars(parProgNB(i))
  /\ WF_vars(coordProg)

SpecNB == InitNB /\ [][NextNB]_vars /\ fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
\* INVALID: all participants eventually commit
AllCommit == \A i \in participants :
                <>(participant[i].decision = commit \/ participant[i].faulty)

\* INVALID: all participants eventually abort
AllAbort == \A i \in participants :
                <>(participant[i].decision = abort \/ participant[i].faulty)

\* INVALID: all commit if everyone voted yes
AllCommitYesVotes ==
  (\A i \in participants : participant[i].vote = yes) =>
     \A i \in participants :
        <>(participant[i].decision = commit \/ participant[i].faulty)

=============================================================================
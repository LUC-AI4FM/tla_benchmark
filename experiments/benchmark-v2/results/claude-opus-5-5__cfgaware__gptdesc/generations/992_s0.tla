------------------------------ MODULE ACP_SB ------------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).             *)
(*                                                                         *)
(* One coordinator and a set of participants.  Synchronous communication   *)
(* has been replaced by implicit asynchronous communication: processes     *)
(* read each other's state.  Failures are detected magically rather than   *)
(* via timeouts.  The broadcast is modeled as a sequence of individual     *)
(* sends that can be interrupted by a coordinator failure.  As a result    *)
(* the protocol is non-terminating and AC5 does not hold.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT participants

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

yes       == "yes"
no        == "no"
undecided == "undecided"
commit    == "commit"
abort     == "abort"
waiting   == "waiting"
notsent   == "notsent"

-----------------------------------------------------------------------------
TypeInvParticipant ==
  participant \in [ participants ->
                      [ vote     : {yes, no},
                        alive    : BOOLEAN,
                        decision : {undecided, commit, abort},
                        faulty   : BOOLEAN,
                        voteSent : BOOLEAN ] ]

TypeInvCoordinator ==
  coordinator \in [ request   : [participants -> BOOLEAN],
                    vote      : [participants -> {waiting, yes, no}],
                    alive     : BOOLEAN,
                    decision  : {undecided, commit, abort},
                    broadcast : [participants -> {notsent, commit, abort}] ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

-----------------------------------------------------------------------------
InitParticipant ==
  participant \in [ participants ->
                      [ vote     : {yes, no},
                        alive    : {TRUE},
                        decision : {undecided},
                        faulty   : {FALSE},
                        voteSent : {FALSE} ] ]

InitCoordinator ==
  coordinator = [ request   |-> [i \in participants |-> FALSE],
                  vote      |-> [i \in participants |-> waiting],
                  alive     |-> TRUE,
                  decision  |-> undecided,
                  broadcast |-> [i \in participants |-> notsent] ]

Init == InitParticipant /\ InitCoordinator

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
  /\ coordinator.request[i]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
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
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~participant[i].voteSent
  /\ ~coordinator.alive
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
  /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                        ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ decide(i)

parProgNdie == \E i \in participants : parProg(i)

coordProgA(i) ==
  \/ request(i)
  \/ getVote(i)
  \/ detectFault(i)
  \/ coordBroadcast(i)

coordProgNdie == makeDecision \/ \E i \in participants : coordProgA(i)

Next ==
  \/ parProgNdie
  \/ coordProgNdie
  \/ coordDie
  \/ \E i \in participants : parDie(i)

Fairness ==
  /\ \A i \in participants :
       /\ WF_vars(sendVote(i))
       /\ WF_vars(abortOnVote(i))
       /\ WF_vars(abortOnTimeoutRequest(i))
       /\ WF_vars(decide(i))
       /\ WF_vars(request(i))
       /\ WF_vars(getVote(i))
       /\ WF_vars(detectFault(i))
       /\ WF_vars(coordBroadcast(i))
  /\ WF_vars(makeDecision)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

NoFailures ==
  coordinator.alive /\ \A i \in participants : participant[i].alive

AC1 ==
  [] \A i, j \in participants :
       ~ /\ participant[i].decision = commit
         /\ participant[j].decision = abort

AC2 ==
  [] \A i \in participants :
       participant[i].decision = commit =>
         \A j \in participants : participant[j].vote = yes

AC3_1 ==
  ( /\ \E j \in participants : participant[j].vote = no
    /\ [] NoFailures )
  => <> \A i \in participants : participant[i].decision = abort

AC3_2 ==
  ( /\ \A j \in participants : participant[j].vote = yes
    /\ [] NoFailures )
  => <> \A i \in participants : participant[i].decision = commit

(* Does NOT hold: broadcast may be interrupted by coordinator failure. *)
AC5 ==
  <> \A i \in participants :
       participant[i].alive => participant[i].decision # undecided

-----------------------------------------------------------------------------
(* Stronger auxiliary properties *)

StrongerAC2 ==
  [] \A i \in participants :
       participant[i].decision = commit =>
         /\ \A j \in participants : participant[j].vote = yes
         /\ coordinator.decision = commit

StrongerAC3_1 ==
  [] /\ (coordinator.decision = commit =>
           \A j \in participants : coordinator.vote[j] = yes)
     /\ \A i \in participants :
          coordinator.vote[i] = yes => participant[i].vote = yes

FaultyStable ==
  \A i \in participants :
    [](participant[i].faulty => [] participant[i].faulty)

VoteStable ==
  \A i \in participants : \A v \in {yes, no} :
    [](participant[i].vote = v => [](participant[i].vote = v))

NoRecovery ==
  /\ [](~coordinator.alive => [] ~coordinator.alive)
  /\ \A i \in participants :
       [](~participant[i].alive => [] ~participant[i].alive)

-----------------------------------------------------------------------------
(* Explicitly invalid properties *)

(* Invalid: an abort may result from a failure even if all voted yes. *)
AbortImpliesNoVote ==
  [] \A i \in participants :
       participant[i].decision = abort =>
         \E j \in participants : participant[j].vote = no

(* Invalid: even if no participant fails, the coordinator may die
   in the middle of its broadcast, leaving participants blocked. *)
DecisionReachedNoFault ==
  (\A i \in participants : [] participant[i].alive)
  => <> \A i \in participants : participant[i].decision # undecided

=============================================================================
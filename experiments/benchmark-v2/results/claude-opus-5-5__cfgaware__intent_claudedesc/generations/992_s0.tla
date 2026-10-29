---------------------------- MODULE ACP_SB ----------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).             *)
(* A single coordinator and a set of participants; asynchronous message   *)
(* passing modeled abstractly; crash failures without recovery; failures  *)
(* detectable abstractly.                                                 *)
(***************************************************************************)

CONSTANTS participants   \* set of participants

VARIABLES participant,   \* participant states
          coordinator    \* coordinator state

vars == <<participant, coordinator>>

yes       == "yes"
no        == "no"
undecided == "undecided"
commit    == "commit"
abort     == "abort"
waiting   == "waiting"
notsent   == "notsent"

---------------------------------------------------------------------------
TypeInvariant ==
  /\ participant \in [participants -> [vote     : {yes, no},
                                       alive    : BOOLEAN,
                                       decision : {undecided, commit, abort},
                                       faulty   : BOOLEAN,
                                       voteSent : BOOLEAN]]
  /\ coordinator \in [request   : [participants -> BOOLEAN],
                      vote      : [participants -> {waiting, yes, no}],
                      broadcast : [participants -> {notsent, commit, abort}],
                      decision  : {undecided, commit, abort},
                      alive     : BOOLEAN,
                      faulty    : BOOLEAN]

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
  /\ participant[i].faulty
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
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

---------------------------------------------------------------------------
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
  /\ coordinator.faulty
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
parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ decide(i)

coordProg ==
  \/ \E i \in participants :
        \/ request(i)
        \/ getVote(i)
        \/ detectFault(i)
        \/ coordBroadcast(i)
  \/ makeDecision

Next ==
  \/ \E i \in participants : parProg(i) \/ parDie(i)
  \/ coordProg
  \/ coordDie

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A i \in participants : WF_vars(parProg(i))
        /\ WF_vars(coordProg)

---------------------------------------------------------------------------
(* Correctness properties *)

\* Agreement
AC1 == [] \A i, j \in participants :
            ~ (participant[i].decision = commit /\ participant[j].decision = abort)

\* Commit validity
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
             => (\A j \in participants : participant[j].vote = yes) )

\* Abort validity
AC3_1 == [] ( (\E i \in participants : participant[i].decision = abort)
               => \/ \E j \in participants : participant[j].vote = no
                  \/ \E j \in participants : participant[j].faulty
                  \/ coordinator.faulty )

\* Progress
AC3_2 == <> ( \/ \A i \in participants : participant[i].decision \in {commit, abort}
              \/ \E j \in participants : participant[j].faulty
              \/ coordinator.faulty )

\* Irrevocability
AC5 == [][ \A i \in participants :
             /\ participant[i].decision = commit => participant'[i].decision = commit
             /\ participant[i].decision = abort  => participant'[i].decision = abort ]_vars

---------------------------------------------------------------------------
(* Auxiliary properties *)

StrongerAC2 == [] ( (\E i \in participants : participant[i].decision = commit)
                     => /\ \A j \in participants : participant[j].vote = yes
                        /\ coordinator.decision = commit )

StrongerAC3_1 == [] \A i \in participants :
                      participant[i].decision = abort
                        => \/ participant[i].vote = no
                           \/ coordinator.decision = abort
                           \/ coordinator.faulty

AbortImpliesNoVote == [] ( coordinator.decision = abort
                            => \/ \E j \in participants : participant[j].vote = no
                               \/ \E j \in participants : participant[j].faulty )

DecisionReachedNoFault ==
  ( /\ coordinator.alive
    /\ \A i \in participants : participant[i].alive )
  ~> ( \/ \A i \in participants : participant[i].decision \in {commit, abort}
       \/ \E j \in participants : participant[j].faulty
       \/ coordinator.faulty )

FaultyStable ==
  /\ \A i \in participants : [](participant[i].faulty => [] participant[i].faulty)
  /\ [](coordinator.faulty => [] coordinator.faulty)

NoRecovery ==
  /\ [] ( /\ coordinator.alive <=> ~coordinator.faulty
          /\ \A i \in participants : participant[i].alive <=> ~participant[i].faulty )
  /\ [][ /\ ~coordinator.alive => ~coordinator'.alive
         /\ \A i \in participants : ~participant[i].alive => ~participant'[i].alive ]_vars

VoteStable == [][ \A i \in participants : participant'[i].vote = participant[i].vote ]_vars

=============================================================================
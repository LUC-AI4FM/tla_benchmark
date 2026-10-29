---------------------------- MODULE ACP_SB ----------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).              *)
(* A coordinator and a set of participants agree on commit/abort.          *)
(* The coordinator broadcasts its decision with simple broadcast: it sends *)
(* the decision to each participant one at a time, and a failure can stop  *)
(* the broadcast partway through.                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS participants

ASSUME participants # {}

yes       == "yes"
no        == "no"
undecided == "undecided"
commit    == "commit"
abort     == "abort"
waiting   == "waiting"

VARIABLES coordinator, participant

vars == <<coordinator, participant>>

---------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
  /\ participant \in [participants ->
        [ vote     : {yes, no},
          alive    : BOOLEAN,
          decision : {undecided, commit, abort},
          faulty   : BOOLEAN,
          voteSent : BOOLEAN ]]
  /\ coordinator \in
        [ request   : [participants -> BOOLEAN],
          vote      : [participants -> {waiting, yes, no}],
          broadcast : [participants -> BOOLEAN],
          decision  : {undecided, commit, abort},
          alive     : BOOLEAN,
          faulty    : BOOLEAN ]

---------------------------------------------------------------------------
(* Initial state *)

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
          broadcast |-> [i \in participants |-> FALSE],
          decision  |-> undecided,
          alive     |-> TRUE,
          faulty    |-> FALSE ]

---------------------------------------------------------------------------
(* Coordinator actions *)

\* Coordinator sends a vote request to participant i
request(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* Coordinator receives the vote of participant i
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.request[i]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* Coordinator detects the failure of participant i while still waiting
\* for its vote, and decides abort
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[i] = waiting
  /\ participant[i].faulty
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Coordinator decides after it has collected all votes
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A i \in participants : coordinator.vote[i] \in {yes, no}
  /\ coordinator' = [coordinator EXCEPT !.decision =
                       IF \A i \in participants : coordinator.vote[i] = yes
                         THEN commit
                         ELSE abort]
  /\ UNCHANGED participant

\* Simple broadcast: send the decision to one participant at a time
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision \in {commit, abort}
  /\ ~coordinator.broadcast[i]
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
  /\ UNCHANGED participant

\* Coordinator fails
coordFail ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

---------------------------------------------------------------------------
(* Participant actions *)

\* Participant i answers the vote request
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* Participant i voted no, so it may abort on its own
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Participant i sees that the coordinator failed before it got a
\* vote request, so it aborts on its own
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.request[i]
  /\ coordinator.faulty
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Participant i receives the broadcast decision from the coordinator
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i]
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
  /\ UNCHANGED coordinator

\* Participant i fails
parFail(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                        ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relation *)

coordProg ==
  \/ makeDecision
  \/ \E i \in participants :
        \/ request(i)
        \/ getVote(i)
        \/ detectFault(i)
        \/ coordBroadcast(i)

parProg ==
  \E i \in participants :
     \/ sendVote(i)
     \/ abortOnVote(i)
     \/ abortOnTimeoutRequest(i)
     \/ decide(i)

Fail ==
  \/ coordFail
  \/ \E i \in participants : parFail(i)

Next == coordProg \/ parProg \/ Fail

\* Weak fairness for every action that is not a failure
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

SomeFaulty ==
  coordinator.faulty \/ \E i \in participants : participant[i].faulty

\* AC1: every participant that decides reaches the same decision
AC1 ==
  [] \A i, j \in participants :
        (participant[i].decision # undecided /\ participant[j].decision # undecided)
          => participant[i].decision = participant[j].decision

\* AC2: a commit requires that every participant voted yes
AC2 ==
  [] ( (\E i \in participants : participant[i].decision = commit)
         => \A j \in participants : participant[j].vote = yes )

\* AC3_1: an abort requires a no vote or some fault
AC3_1 ==
  [] ( (\E i \in participants : participant[i].decision = abort)
         => \/ \E j \in participants : participant[j].vote = no
            \/ SomeFaulty )

\* AC4: decisions cannot be revoked
AC4 ==
  [][ \A i \in participants :
        participant[i].decision # undecided
          => participant'[i].decision = participant[i].decision ]_vars

\* AC3_2: eventually every participant decides, or some process is faulty
AC3_2 ==
  <> ( (\A i \in participants : participant[i].decision \in {commit, abort})
       \/ SomeFaulty )

(***************************************************************************)
(* AC5 would say that all participants eventually decide even when faults  *)
(* occur. AC5 does NOT hold for ACP-SB. With simple broadcast, the         *)
(* coordinator can fail partway through sending its decision. A            *)
(* participant that voted yes and got no broadcast then stays undecided    *)
(* forever.                                                                *)
(*                                                                         *)
(* AC5 == <> \A i \in participants :                                       *)
(*           participant[i].alive => participant[i].decision # undecided   *)
(***************************************************************************)

THEOREM Spec => /\ []TypeOK
                /\ AC1 /\ AC2 /\ AC3_1 /\ AC4 /\ AC3_2

=============================================================================
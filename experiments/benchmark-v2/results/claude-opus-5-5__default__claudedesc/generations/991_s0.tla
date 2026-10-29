------------------------------ MODULE MC_ACP_SB ------------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with Simple Broadcast (ACP_SB), set up for   *)
(* model checking with TLC.                                                *)
(*                                                                         *)
(* The base specification ACP_SB is included inline so that this module   *)
(* is self-contained. It adds:                                             *)
(*   - a symmetry set over participants                                   *)
(*   - AC4_alt, a reformulation of AC4 that TLC checks more efficiently.  *)
(*                                                                         *)
(* Suggested TLC configuration:                                           *)
(*   CONSTANTS participants = {p1, p2, p3}                                 *)
(*             yes = yes  no = no  undecided = undecided                   *)
(*             commit = commit  abort = abort                              *)
(*             waiting = waiting  notsent = notsent                        *)
(*   SPECIFICATION Spec                                                    *)
(*   SYMMETRY      SymmetricParticipants                                   *)
(*   INVARIANTS    TypeInv AC1 AC2 AC3_1                                   *)
(*   PROPERTIES    AC4_alt AC3_2                                           *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants,                    \* set of participants
          yes, no,                         \* votes
          undecided, commit, abort,        \* decisions
          waiting,                         \* coordinator still waiting for a vote
          notsent                          \* coordinator has not yet broadcast

ASSUME /\ participants # {}
       /\ Cardinality({yes, no, undecided, commit, abort, waiting, notsent}) = 7

VARIABLES participant,   \* participant state, indexed by participant
          coordinator    \* coordinator state

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(* Type invariants *)

TypeInvParticipant ==
  participant \in [participants ->
                     [vote     : {yes, no},
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
(* Initial state *)

InitParticipant ==
  participant \in [participants ->
                     [vote     : {yes, no},
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

\* Coordinator sends a vote request to participant i
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* Coordinator receives the vote of participant i
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* Coordinator detects failure of participant i that has not sent its vote;
\* the missing vote is treated as "no"
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.request[i]
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
  /\ UNCHANGED participant

\* Coordinator decides once all votes are known
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ coordinator' = [coordinator EXCEPT !.decision =
                        IF \A j \in participants : coordinator.vote[j] = yes
                          THEN commit ELSE abort]
  /\ UNCHANGED participant

\* Coordinator sends its decision to participant i (simple broadcast)
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

\* Coordinator crashes
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

---------------------------------------------------------------------------
(* Participant actions *)

\* Participant i sends its vote after receiving a request
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* A participant that voted "no" may abort unilaterally
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* A participant that never received a request and detects that the
\* coordinator has crashed may abort
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Participant i receives the coordinator's decision
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] \in {commit, abort}
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

\* Participant i crashes
parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relation and specification *)

coordProg(i) == request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

parProg(i) == sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i) \/ decide(i)

Next ==
  \/ makeDecision
  \/ coordDie
  \/ \E i \in participants : coordProg(i) \/ parProg(i) \/ parDie(i)

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
(* Correctness properties *)

\* AC1: all participants that decide reach the same decision
AC1 == \A i, j \in participants :
         \/ participant[i].decision # commit
         \/ participant[j].decision # abort

\* AC2: if any participant decides commit, then all participants voted yes
AC2 == (\E i \in participants : participant[i].decision = commit)
         => (\A j \in participants : participant[j].vote = yes)

\* AC3_1: if all participants vote yes and there are no failures,
\* then no participant decides abort
AC3_1 == ( /\ \A i \in participants : participant[i].vote = yes
           /\ \A i \in participants : ~participant[i].faulty
           /\ ~coordinator.faulty )
         => (\A i \in participants : participant[i].decision # abort)

\* AC3_2: if there are no failures, eventually all participants decide
AC3_2 == ( /\ [](\A i \in participants : ~participant[i].faulty)
           /\ []~coordinator.faulty )
         => <>(\A i \in participants : participant[i].decision \in {commit, abort})

\* AC4: decisions are irrevocable
AC4 == \A i \in participants :
         /\ [](participant[i].decision = commit => [](participant[i].decision = commit))
         /\ [](participant[i].decision = abort  => [](participant[i].decision = abort))

\* AC4_alt: equivalent action-level formulation, more efficient for TLC
AC4_alt == [][ \A i \in participants :
                 participant[i].decision \in {commit, abort}
                   => participant'[i].decision = participant[i].decision ]_vars

---------------------------------------------------------------------------
(* Intermediate properties *)

\* The coordinator only decides commit if all votes are yes
CoordCommitImpliesAllYes ==
  coordinator.decision = commit => \A i \in participants : coordinator.vote[i] = yes

\* A broadcast decision always matches the coordinator's decision
BroadcastConsistent ==
  \A i \in participants :
    coordinator.broadcast[i] # notsent => coordinator.broadcast[i] = coordinator.decision

\* A participant that decided commit agrees with the coordinator
ParticipantAgreesWithCoord ==
  \A i \in participants :
    participant[i].decision = commit => coordinator.decision = commit

---------------------------------------------------------------------------
(* Deliberately invalid properties (sanity checks; TLC should report a     *)
(* violation)                                                              *)

\* Fails: with simple broadcast, alive participants may block forever if
\* the coordinator crashes after requesting votes
AC5_invalid == <>(\A i \in participants :
                    participant[i].alive => participant[i].decision \in {commit, abort})

\* Fails: some runs end with an abort
AlwaysCommit_invalid == \A i \in participants : participant[i].decision # abort

\* Fails: some runs end with a commit
NeverCommit_invalid == \A i \in participants : participant[i].decision # commit

---------------------------------------------------------------------------
(* Symmetry for TLC *)

SymmetricParticipants == Permutations(participants)

=============================================================================
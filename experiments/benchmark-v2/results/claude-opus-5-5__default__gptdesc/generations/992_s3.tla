------------------------------- MODULE ACP_SB -------------------------------
(***************************************************************************)
(* Atomic commitment protocol with one coordinator and a set of            *)
(* participants, using a simple broadcast (SB) for the decision.           *)
(*                                                                         *)
(* - Synchronous communication has been replaced by implicit asynchronous  *)
(*   communication: processes read and write shared state directly.        *)
(* - Failures are detected "magically" (a process can see that another     *)
(*   one is dead) rather than through timeouts.                            *)
(* - Broadcast is modeled as a sequence of individual sends.  The          *)
(*   coordinator can fail part way through, so some participants that      *)
(*   voted yes may block forever.  The protocol is therefore               *)
(*   non-terminating and the usual termination property AC5 does not hold. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no,        \* votes
    undecided, commit, abort,  \* decisions
    waiting,        \* coordinator has not yet received a vote
    notsent         \* coordinator has not yet sent its decision

VARIABLES
    participant,    \* function from participants to participant records
    coordinator     \* coordinator record

vars == <<participant, coordinator>>

ASSUME
    /\ participants # {}
    /\ Cardinality({yes, no, undecided, commit, abort, waiting, notsent}) = 7

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
ParticipantType ==
    [ vote     : {yes, no},
      alive    : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty   : BOOLEAN,
      voteSent : BOOLEAN ]

CoordinatorType ==
    [ request   : [participants -> BOOLEAN],
      vote      : [participants -> {waiting, yes, no}],
      broadcast : [participants -> {notsent, commit, abort}],
      decision  : {undecided, commit, abort},
      alive     : BOOLEAN,
      faulty    : BOOLEAN ]

TypeOK ==
    /\ participant \in [participants -> ParticipantType]
    /\ coordinator \in CoordinatorType

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial states: votes are chosen nondeterministically, everyone alive.  *)
(***************************************************************************)
InitParticipant ==
    participant \in [participants ->
                        [ vote     : {yes, no},
                          alive    : {TRUE},
                          decision : {undecided},
                          faulty   : {FALSE},
                          voteSent : {FALSE} ]]

InitCoordinator ==
    coordinator \in [ request   : {[i \in participants |-> FALSE]},
                      vote      : {[i \in participants |-> waiting]},
                      broadcast : {[i \in participants |-> notsent]},
                      decision  : {undecided},
                      alive     : {TRUE},
                      faulty    : {FALSE} ]

Init == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
(***************************************************************************)
(* Participant actions                                                     *)
(***************************************************************************)

\* Participant i sends its vote after receiving the vote request.
sendVote(i) ==
    /\ participant[i].alive
    /\ coordinator.request[i]
    /\ ~participant[i].voteSent
    /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
    /\ coordinator' = [coordinator EXCEPT ![i] = @, !.vote[i] = participant[i].vote]

\* A participant that voted no may abort unilaterally.
abortOnVote(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[i].voteSent
    /\ participant[i].vote = no
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

\* Coordinator died before requesting the vote: participant may abort.
abortOnTimeoutRequest(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ ~coordinator.request[i]
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

\* Participant receives the coordinator's decision.
parDecide(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ coordinator.broadcast[i] # notsent
    /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
    /\ UNCHANGED coordinator

\* Participant failure.
parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

parProg(i) ==
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ parDecide(i)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)

\* Coordinator sends the vote request to participant i.
request(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
    /\ UNCHANGED participant

\* Coordinator decides once all votes have arrived.
coordDecide ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A i \in participants : coordinator.vote[i] # waiting
    /\ coordinator' = [coordinator EXCEPT
                         !.decision = IF \A i \in participants : coordinator.vote[i] = yes
                                      THEN commit ELSE abort]
    /\ UNCHANGED participant

\* Coordinator (magically) detects that a participant died before voting.
abortOnTimeoutVote ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \E i \in participants :
          /\ coordinator.vote[i] = waiting
          /\ participant[i].faulty
    /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED participant

\* One step of the simple broadcast: send decision to participant i.
coordBroadcast(i) ==
    /\ coordinator.alive
    /\ coordinator.decision # undecided
    /\ coordinator.broadcast[i] = notsent
    /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
    /\ UNCHANGED participant

\* Coordinator failure.
coordDie ==
    /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
    /\ UNCHANGED participant

coordProg ==
    \/ \E i \in participants : request(i)
    \/ coordDecide
    \/ abortOnTimeoutVote
    \/ \E i \in participants : coordBroadcast(i)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
parN    == \E i \in participants : parProg(i) \/ parDie(i)
coordN  == coordProg \/ coordDie

Next == parN \/ coordN

Fairness ==
    /\ \A i \in participants : WF_vars(parProg(i))
    /\ WF_vars(coordProg)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* AC1: all participants that decide reach the same decision.
AC1 == [] \A i, j \in participants :
            ~(participant[i].decision = commit /\ participant[j].decision = abort)

\* AC2: if any participant decides commit, then all participants voted yes.
AC2 == [] ((\E i \in participants : participant[i].decision = commit)
              => (\A j \in participants : participant[j].vote = yes))

\* AC3_1: if any participant decides abort, then some participant voted no,
\* or some process failed.
AC3_1 == [] ((\E i \in participants : participant[i].decision = abort)
               => \/ \E j \in participants : participant[j].vote = no
                  \/ \E j \in participants : participant[j].faulty
                  \/ coordinator.faulty)

\* AC4: decisions are irreversible.
AC4 == [] \A i \in participants :
            /\ (participant[i].decision = commit => [](participant[i].decision = commit))
            /\ (participant[i].decision = abort  => [](participant[i].decision = abort))

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* AC3_2: if all vote yes and no failures occur, all participants commit.
AC3_2 == <> \/ \A i \in participants : participant[i].decision = commit
            \/ \E i \in participants : participant[i].vote = no
            \/ \E i \in participants : participant[i].faulty
            \/ coordinator.faulty

\* If nobody ever fails, every participant eventually decides.
AC3_3 == ([] (/\ \A i \in participants : ~participant[i].faulty
              /\ ~coordinator.faulty))
           => <> (\A i \in participants : participant[i].decision # undecided)

(***************************************************************************)
(* Stronger auxiliary properties (invariants)                              *)
(***************************************************************************)

\* A participant commits only if the coordinator decided commit.
StrongerAC1 ==
    \A i \in participants :
        /\ participant[i].decision = commit =>
              /\ coordinator.decision = commit
              /\ coordinator.broadcast[i] = commit
        /\ (participant[i].decision = abort /\ participant[i].vote = yes) =>
              coordinator.decision # commit

\* Coordinator commits only if every participant voted yes.
StrongerAC2 ==
    /\ coordinator.decision = commit =>
          \A j \in participants :
              /\ participant[j].vote = yes
              /\ coordinator.vote[j] = yes
    /\ \A i \in participants :
          coordinator.broadcast[i] # notsent =>
              coordinator.broadcast[i] = coordinator.decision

\* Abort only on a no vote or a failure.
StrongerAC3_1 ==
    /\ coordinator.decision = abort =>
          \/ \E j \in participants : participant[j].vote = no
          \/ \E j \in participants : participant[j].faulty
    /\ \A i \in participants :
          participant[i].decision = abort =>
              \/ participant[i].vote = no
              \/ coordinator.decision = abort
              \/ coordinator.faulty

\* Received votes reflect true votes.
VoteConsistent ==
    \A i \in participants :
        coordinator.vote[i] # waiting =>
            /\ coordinator.vote[i] = participant[i].vote
            /\ participant[i].voteSent

\* Faulty flags are consistent with liveness.
FaultConsistent ==
    /\ \A i \in participants : participant[i].faulty = ~participant[i].alive
    /\ coordinator.faulty = ~coordinator.alive

StrongerInv ==
    /\ TypeOK
    /\ StrongerAC1
    /\ StrongerAC2
    /\ StrongerAC3_1
    /\ VoteConsistent
    /\ FaultConsistent

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invalid properties (expected to be violated)                            *)
(***************************************************************************)

\* AC5: every live participant eventually decides.  Fails because the
\* coordinator may die in the middle of its broadcast, blocking
\* participants that voted yes.
AC5 == \A i \in participants :
          <> (\/ participant[i].decision # undecided
              \/ participant[i].faulty)

\* Not every participant is guaranteed to eventually commit.
InvalidAllCommit ==
    <> (\A i \in participants : participant[i].decision = commit)

\* Termination of the coordinator's broadcast is not guaranteed.
InvalidBroadcastCompletes ==
    <> (\A i \in participants : coordinator.broadcast[i] # notsent)

=============================================================================
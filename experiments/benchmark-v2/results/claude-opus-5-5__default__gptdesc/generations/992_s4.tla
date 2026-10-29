---------------------------- MODULE ACP_SB ----------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with Simple Broadcast (ACP_SB).              *)
(*                                                                         *)
(* One coordinator and a set of participants.                              *)
(*                                                                         *)
(*  - Synchronous communication has been replaced by implicit asynchronous *)
(*    communication: a process reads the state of another process          *)
(*    directly.                                                            *)
(*  - Failures are detected "magically" by reading the alive/faulty flags  *)
(*    of other processes, rather than by timeouts.                         *)
(*  - The coordinator broadcasts its decision as a sequence of individual  *)
(*    sends, one per participant. A coordinator failure can interrupt this *)
(*    sequence. Participants that miss the decision then wait forever.     *)
(*    The protocol is therefore non-terminating, and AC5 does not hold.    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
  participants,              \* set of participants
  yes, no,                   \* votes
  undecided, commit, abort,  \* decisions
  waiting,                   \* coordinator state wrt a participant's vote
  notsent                    \* broadcast state

ASSUME
  /\ yes # no
  /\ undecided # commit /\ undecided # abort /\ commit # abort
  /\ waiting \notin {yes, no}
  /\ notsent \notin {commit, abort}

VARIABLES
  participant,   \* the participants
  coordinator    \* the coordinator

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(* Type invariants *)

TypeInvParticipant ==
  participant \in [participants ->
                     [ vote     : {yes, no},
                       alive    : BOOLEAN,
                       decision : {undecided, commit, abort},
                       faulty   : BOOLEAN,
                       voteSent : BOOLEAN ]]

TypeInvCoordinator ==
  coordinator \in [ request   : [participants -> BOOLEAN],
                    vote      : [participants -> {waiting, yes, no}],
                    alive     : BOOLEAN,
                    decision  : {undecided, commit, abort},
                    broadcast : [participants -> {commit, abort, notsent}] ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

---------------------------------------------------------------------------
(* Initial states *)

InitParticipant ==
  participant \in [participants ->
                     [ vote     : {yes, no},
                       alive    : {TRUE},
                       decision : {undecided},
                       faulty   : {FALSE},
                       voteSent : {FALSE} ]]

InitCoordinator ==
  coordinator \in [ request   : [participants -> {FALSE}],
                    vote      : [participants -> {waiting}],
                    alive     : {TRUE},
                    decision  : {undecided},
                    broadcast : [participants -> {notsent}] ]

Init == InitParticipant /\ InitCoordinator

---------------------------------------------------------------------------
(* Coordinator actions *)

\* Send a vote request to participant i.
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* Receive the vote of participant i.
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* Magically detect that participant i failed before sending its vote.
\* Treat the missing vote as "no".
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].faulty
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
  /\ UNCHANGED participant

\* Decide once all votes are known.
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Simple broadcast: send the decision to participant i.
\* A coordinator failure may interrupt the broadcast.
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

\* The coordinator fails.
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

---------------------------------------------------------------------------
(* Participant actions *)

\* Send the vote to the coordinator after receiving a request.
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* A participant that votes "no" may abort unilaterally.
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Magically detect a coordinator failure before a request arrives, then abort.
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Receive the decision broadcast by the coordinator.
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] \in {commit, abort}
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

\* Participant i fails.
parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relation *)

parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ decide(i)

parProgNext == \E i \in participants : parProg(i)

coordProgA(i) ==
  \/ request(i)
  \/ getVote(i)
  \/ detectFault(i)
  \/ coordBroadcast(i)

coordProgB == makeDecision

coordProgNext == (\E i \in participants : coordProgA(i)) \/ coordProgB

parFailNext   == \E i \in participants : parDie(i)
coordFailNext == coordDie

Next ==
  \/ parProgNext
  \/ coordProgNext
  \/ parFailNext
  \/ coordFailNext

\* Weak fairness on all progress actions. Death actions get no fairness.
Fairness ==
  /\ \A i \in participants : WF_vars(parProg(i))
  /\ \A i \in participants : WF_vars(coordProgA(i))
  /\ WF_vars(coordProgB)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Correctness properties *)

\* AC1: all participants that decide reach the same decision.
AC1 ==
  [] \A i, j \in participants :
       ~(participant[i].decision = commit /\ participant[j].decision = abort)

\* AC2: a participant commits only if all participants voted yes.
AC2 ==
  [] ( (\E i \in participants : participant[i].decision = commit)
         => (\A j \in participants : participant[j].vote = yes) )

\* AC3_1: if any participant votes no, then no participant commits.
AC3_1 ==
  [] ( (\E i \in participants : participant[i].vote = no)
         => (\A j \in participants : participant[j].decision # commit) )

\* AC3_2: with no failures and only yes votes, everyone eventually commits.
AC3_2 ==
  <> ( ( /\ coordinator.alive
         /\ \A i \in participants : participant[i].alive
         /\ \A i \in participants : participant[i].vote = yes )
       => (\A i \in participants : participant[i].decision = commit) )

\* AC4: decisions are irreversible.
AC4 ==
  /\ \A i \in participants :
       [] ( participant[i].decision = commit => [](participant[i].decision = commit) )
  /\ \A i \in participants :
       [] ( participant[i].decision = abort  => [](participant[i].decision = abort) )

---------------------------------------------------------------------------
(* Stronger auxiliary properties *)

\* The coordinator never commits when some participant has aborted.
AC1_strong ==
  [] \A i \in participants :
       ~(coordinator.decision = commit /\ participant[i].decision = abort)

\* A committing participant always agrees with the coordinator.
CommitImpliesCoordCommit ==
  [] \A i \in participants :
       participant[i].decision = commit => coordinator.decision = commit

\* The coordinator commits only if all participants voted yes.
CoordCommitImpliesAllYes ==
  [] ( coordinator.decision = commit
         => \A i \in participants : participant[i].vote = yes )

\* The coordinator's recorded votes match the participants' votes.
CoordVotesCorrect ==
  [] \A i \in participants :
       coordinator.vote[i] = yes => participant[i].vote = yes

\* Any broadcast message equals the coordinator's decision.
BroadcastConsistent ==
  [] \A i \in participants :
       coordinator.broadcast[i] # notsent
         => coordinator.broadcast[i] = coordinator.decision

\* The coordinator eventually decides as long as it stays alive.
CoordDecidesIfAlive ==
  <>[]( coordinator.alive ) => <>( coordinator.decision # undecided )

---------------------------------------------------------------------------
(* Explicitly INVALID properties for this protocol *)

\* AC5 (termination): every live participant eventually decides.
\* This fails because a coordinator crash can interrupt the broadcast.
AC5 ==
  <> \A i \in participants :
       participant[i].alive => participant[i].decision # undecided

\* Invalid: an abort does not imply that someone voted no
\* (timeouts and failures also cause aborts).
AbortImpliesNoVote ==
  [] ( (\E i \in participants : participant[i].decision = abort)
         => (\E j \in participants : participant[j].vote = no) )

\* Invalid: participants do not eventually all reach the same decision.
AllEventuallyAgree ==
  <> \A i, j \in participants :
       participant[i].decision = participant[j].decision

THEOREM Spec => [] TypeInv
THEOREM Spec => AC1 /\ AC2 /\ AC3_1 /\ AC4
=============================================================================
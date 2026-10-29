------------------------------- MODULE ACP_SB -------------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with Simple Broadcast (ACP-SB).              *)
(*                                                                         *)
(* A single coordinator and a set of participants decide whether to       *)
(* commit or abort a transaction. Communication is asynchronous and is    *)
(* modeled abstractly through shared state:                                *)
(*  - coordinator.request[i]   : vote request sent to participant i        *)
(*  - participant[i].voteSent  : participant i sent its vote               *)
(*  - coordinator.vote[i]      : vote of i as received by the coordinator  *)
(*  - coordinator.broadcast[i] : decision sent to participant i            *)
(* Failures are crash failures with no recovery. Failure detection is      *)
(* modeled by reading the "alive" flag of other processes.                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT Participants

ASSUME Participants # {} /\ IsFiniteSet(Participants)

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

Votes         == {"yes", "no"}
Decisions     == {"undecided", "commit", "abort"}
CoordVotes    == {"waiting", "yes", "no"}
BroadcastVals == {"notsent", "commit", "abort"}

-----------------------------------------------------------------------------
TypeOK ==
  /\ participant \in [Participants ->
                        [vote     : Votes,
                         alive    : BOOLEAN,
                         decision : Decisions,
                         voteSent : BOOLEAN]]
  /\ coordinator \in [request   : [Participants -> BOOLEAN],
                      vote      : [Participants -> CoordVotes],
                      broadcast : [Participants -> BroadcastVals],
                      decision  : Decisions,
                      alive     : BOOLEAN]

Init ==
  /\ participant \in [Participants ->
                        [vote     : Votes,
                         alive    : {TRUE},
                         decision : {"undecided"},
                         voteSent : {FALSE}]]
  /\ coordinator = [request   |-> [i \in Participants |-> FALSE],
                    vote      |-> [i \in Participants |-> "waiting"],
                    broadcast |-> [i \in Participants |-> "notsent"],
                    decision  |-> "undecided",
                    alive     |-> TRUE]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Coordinator actions                                                      *)
(***************************************************************************)

\* Coordinator sends a vote request to participant i
CoordSendRequest(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* Coordinator receives the vote of participant i
CoordGetVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ coordinator.vote[i] = "waiting"
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* Coordinator decides commit: all participants voted yes
CoordDecideCommit ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ \A i \in Participants : coordinator.vote[i] = "yes"
  /\ coordinator' = [coordinator EXCEPT !.decision = "commit"]
  /\ UNCHANGED participant

\* Coordinator decides abort: some participant voted no or has failed
CoordDecideAbort ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ \E i \in Participants :
        \/ coordinator.vote[i] = "no"
        \/ ~participant[i].alive
  /\ coordinator' = [coordinator EXCEPT !.decision = "abort"]
  /\ UNCHANGED participant

CoordDecide == CoordDecideCommit \/ CoordDecideAbort

\* Simple broadcast: the decision is sent to one participant at a time
CoordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # "undecided"
  /\ coordinator.broadcast[i] = "notsent"
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

\* Coordinator crashes (permanently)
CoordFail ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

-----------------------------------------------------------------------------
(***************************************************************************)
(* Participant actions                                                      *)
(***************************************************************************)

\* Participant i answers the vote request
ParVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* Participant i adopts the decision received from the coordinator
ParDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ coordinator.broadcast[i] # "notsent"
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

\* Participant i that votes no may unilaterally abort
ParAbortOnNo(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ participant[i].vote = "no"
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

\* Participant i detects coordinator failure before receiving a vote request
ParAbortOnCoordFail(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

\* Participant i crashes (permanently)
ParFail(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
CoordProg ==
  \/ \E i \in Participants : CoordSendRequest(i)
  \/ \E i \in Participants : CoordGetVote(i)
  \/ CoordDecide
  \/ \E i \in Participants : CoordBroadcast(i)

ParProg(i) ==
  \/ ParVote(i)
  \/ ParDecide(i)
  \/ ParAbortOnNo(i)
  \/ ParAbortOnCoordFail(i)

Next ==
  \/ CoordProg
  \/ CoordFail
  \/ \E i \in Participants : ParProg(i)
  \/ \E i \in Participants : ParFail(i)

Fairness ==
  /\ \A i \in Participants :
        /\ WF_vars(ParVote(i))
        /\ WF_vars(ParDecide(i))
        /\ WF_vars(ParAbortOnNo(i))
        /\ WF_vars(ParAbortOnCoordFail(i))
  /\ \A i \in Participants :
        /\ WF_vars(CoordSendRequest(i))
        /\ WF_vars(CoordGetVote(i))
        /\ WF_vars(CoordBroadcast(i))
  /\ WF_vars(CoordDecide)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                   *)
(***************************************************************************)

\* 1. Agreement: no participant commits while another aborts
AC1 ==
  \A i, j \in Participants :
     ~(participant[i].decision = "commit" /\ participant[j].decision = "abort")

\* 2. Commit validity: commit only if all participants voted yes
AC2 ==
  (\E i \in Participants : participant[i].decision = "commit")
     => (\A j \in Participants : participant[j].vote = "yes")

\* 3. Abort validity: abort only if some no vote or some failure
AC3 ==
  (\E i \in Participants : participant[i].decision = "abort")
     => \/ \E j \in Participants : participant[j].vote = "no"
        \/ \E j \in Participants : ~participant[j].alive
        \/ ~coordinator.alive

\* 4. Irrevocability: decisions never change once made
AC4 ==
  [][\A i \in Participants :
        participant[i].decision # "undecided"
           => participant'[i].decision = participant[i].decision]_vars

\* 5. Progress: eventually all decide, or some process has failed
AC5 ==
  <>( \/ \A i \in Participants : participant[i].decision # "undecided"
      \/ \E i \in Participants : ~participant[i].alive
      \/ ~coordinator.alive )

Safety == TypeOK /\ AC1 /\ AC2 /\ AC3

THEOREM Spec => [](TypeOK /\ AC1 /\ AC2 /\ AC3)
THEOREM Spec => AC4
THEOREM Spec => AC5

=============================================================================
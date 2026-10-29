------------------------------ MODULE ACP_SB ------------------------------
(***************************************************************************)
(* Atomic commitment for one coordinator and a set of participants.       *)
(* Communication is asynchronous and point-to-point. The coordinator      *)
(* broadcasts its decision with a simple broadcast primitive, modeled as  *)
(* one send per participant, so a crash part-way through the broadcast    *)
(* means some participants never receive it. Processes may crash (stop    *)
(* failures) and never recover. Failure detection is modeled abstractly.  *)
(* A termination rule lets live participants decide once the coordinator  *)
(* has crashed, which keeps the protocol non-blocking.                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS participants        \* set of participant identifiers

VARIABLES participant,        \* local state of each participant
          coordinator         \* local state of the coordinator

vars == <<participant, coordinator>>

Votes     == {"yes", "no"}
Decisions == {"undecided", "commit", "abort"}

-----------------------------------------------------------------------------
(* Legal state space *)

TypeOKParticipant ==
  participant \in [participants ->
                     [ vote     : Votes,
                       alive    : BOOLEAN,
                       decision : Decisions,
                       faulty   : BOOLEAN,
                       voteSent : BOOLEAN ]]

TypeOKCoordinator ==
  coordinator \in [ request   : [participants -> BOOLEAN],
                    vote      : [participants -> {"waiting", "yes", "no"}],
                    broadcast : [participants -> {"commit", "abort", "notsent"}],
                    decision  : Decisions,
                    alive     : BOOLEAN,
                    faulty    : BOOLEAN ]

TypeOK == TypeOKParticipant /\ TypeOKCoordinator

-----------------------------------------------------------------------------
(* Initial conditions *)

InitParticipant ==
  participant \in [participants ->
                     [ vote     : Votes,
                       alive    : {TRUE},
                       decision : {"undecided"},
                       faulty   : {FALSE},
                       voteSent : {FALSE} ]]

InitCoordinator ==
  coordinator = [ request   |-> [i \in participants |-> FALSE],
                  vote      |-> [i \in participants |-> "waiting"],
                  broadcast |-> [i \in participants |-> "notsent"],
                  decision  |-> "undecided",
                  alive     |-> TRUE,
                  faulty    |-> FALSE ]

Init == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
(* Coordinator actions *)

\* Send a vote request to participant i.
Request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* Receive the vote of participant i (the message may arrive even if i has
\* crashed after sending).
GetVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = "waiting"
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* Detect that participant i crashed before sending its vote: count it as "no".
DetectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = "waiting"
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = "no"]
  /\ UNCHANGED participant

\* Decide once every vote has been collected.
MakeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ \A j \in participants : coordinator.vote[j] # "waiting"
  /\ coordinator' = [coordinator EXCEPT !.decision =
                        IF \A j \in participants : coordinator.vote[j] = "yes"
                        THEN "commit" ELSE "abort"]
  /\ UNCHANGED participant

\* One step of the simple broadcast: send the decision to participant i.
CoordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # "undecided"
  /\ coordinator.broadcast[i] = "notsent"
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

\* The coordinator crashes; it never recovers.
CoordFail ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

-----------------------------------------------------------------------------
(* Participant actions *)

\* Reply to a vote request.
SendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* A participant that voted "no" may abort unilaterally.
AbortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ participant[i].voteSent
  /\ participant[i].vote = "no"
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

\* Adopt the decision received from the coordinator's broadcast.
DecideOnBroadcast(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ coordinator.broadcast[i] # "notsent"
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

\* Termination rule after the coordinator's crash is detected (abstractly).
\* If some decision message was sent before the crash, the participant learns
\* that decision from its peers. Otherwise nobody can commit, so it aborts.
\* This also covers the case where the coordinator crashed before sending
\* the request.
Terminate(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ ~coordinator.alive
  /\ participant' = [participant EXCEPT ![i].decision =
                        IF \E j \in participants : coordinator.broadcast[j] # "notsent"
                        THEN coordinator.decision
                        ELSE "abort"]
  /\ UNCHANGED coordinator

\* Participant i crashes; it never recovers.
ParticipantFail(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

\* Termination: every participant has decided or crashed (avoids spurious deadlock).
Done ==
  /\ \A i \in participants :
        participant[i].decision # "undecided" \/ ~participant[i].alive
  /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Specification *)

Next ==
  \/ \E i \in participants :
        \/ Request(i) \/ GetVote(i) \/ DetectFault(i) \/ CoordBroadcast(i)
        \/ SendVote(i) \/ AbortOnVote(i) \/ DecideOnBroadcast(i)
        \/ Terminate(i) \/ ParticipantFail(i)
  \/ MakeDecision
  \/ CoordFail
  \/ Done

Fairness ==
  /\ \A i \in participants :
        /\ WF_vars(Request(i))
        /\ WF_vars(GetVote(i))
        /\ WF_vars(DetectFault(i))
        /\ WF_vars(CoordBroadcast(i))
        /\ WF_vars(SendVote(i))
        /\ WF_vars(AbortOnVote(i))
        /\ WF_vars(DecideOnBroadcast(i))
        /\ WF_vars(Terminate(i))
  /\ WF_vars(MakeDecision)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Helper predicates *)

NoFault ==
  /\ ~coordinator.faulty
  /\ \A i \in participants : ~participant[i].faulty

SomeFault ==
  \/ coordinator.faulty
  \/ \E j \in participants : participant[j].faulty

-----------------------------------------------------------------------------
(* Safety properties *)

\* AC1: agreement. No two participants decide differently.
AC1 == [] \A i, j \in participants :
            ~(participant[i].decision = "commit" /\ participant[j].decision = "abort")

\* AC4: a decision, once taken, never changes.
AC4 == [][\A i \in participants :
             participant[i].decision # "undecided" =>
                participant'[i].decision = participant[i].decision]_vars

\* AC2: validity. Commit only if every participant voted yes.
AC2 == [] \A i \in participants :
            participant[i].decision = "commit" =>
               \A j \in participants : participant[j].vote = "yes"

\* Stronger version: every yes vote was actually sent and the coordinator decided commit.
StrongerAC2 == [] \A i \in participants :
            participant[i].decision = "commit" =>
               /\ coordinator.decision = "commit"
               /\ \A j \in participants :
                     /\ participant[j].vote = "yes"
                     /\ participant[j].voteSent
                     /\ coordinator.vote[j] = "yes"

\* AC3_1: an abort is explained by a no vote or by some crash.
AC3_1 == [] \A i \in participants :
            participant[i].decision = "abort" =>
               \/ \E j \in participants : participant[j].vote = "no"
               \/ SomeFault

\* Stronger version: the no vote was actually sent.
StrongerAC3_1 == [] \A i \in participants :
            participant[i].decision = "abort" =>
               \/ \E j \in participants :
                     participant[j].vote = "no" /\ participant[j].voteSent
               \/ \E j \in participants : participant[j].faulty
               \/ coordinator.faulty

\* Auxiliary: an abort comes from a no vote known to the coordinator or to a
\* participant, or from the coordinator's crash.
AbortImpliesNoVote == []
  /\ (coordinator.decision = "abort" =>
         \E j \in participants : coordinator.vote[j] = "no")
  /\ \A i \in participants :
        participant[i].decision = "abort" =>
           \/ coordinator.faulty
           \/ \E j \in participants :
                 coordinator.vote[j] = "no" \/ participant[j].vote = "no"

-----------------------------------------------------------------------------
(* Auxiliary stability properties *)

FaultyStable ==
  [][ /\ \A i \in participants : participant[i].faulty => participant'[i].faulty
      /\ coordinator.faulty => coordinator'.faulty ]_vars

NoRecovery ==
  [][ /\ \A i \in participants : ~participant[i].alive => ~participant'[i].alive
      /\ ~coordinator.alive => ~coordinator'.alive ]_vars

VoteStable ==
  [][ \A i \in participants : participant'[i].vote = participant[i].vote ]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* AC3_2: if all vote yes and no failure ever occurs, everyone commits.
AC3_2 ==
  ( (\A i \in participants : participant[i].vote = "yes") /\ []NoFault )
     => <>(\A i \in participants : participant[i].decision = "commit")

\* AC5: crashes are stable and finite, so failures eventually stop; every
\* live participant then eventually decides.
AC5 == <>(\A i \in participants :
             participant[i].alive => participant[i].decision # "undecided")

\* With no failures at all, every participant eventually decides.
DecisionReachedNoFault ==
  []NoFault => <>(\A i \in participants : participant[i].decision # "undecided")

=============================================================================
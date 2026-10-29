------------------------------ MODULE ACP_NB ------------------------------
(***************************************************************************)
(* Non-blocking atomic commitment protocol for a fixed set of             *)
(* participants and one coordinator, in a synchronous fault model.        *)
(*                                                                         *)
(*  - Each participant starts with a nondeterministic vote (yes / no).    *)
(*  - The coordinator requests votes and collects them. It detects        *)
(*    crashed participants through perfect failure detection             *)
(*    (synchronous timeouts). It then decides and broadcasts.            *)
(*  - Steps are interleaved asynchronously, so message delivery order is  *)
(*    nondeterministic.                                                   *)
(*  - Any participant and the coordinator may crash (crash-stop).        *)
(*  - A participant relays its decision to every participant atomically  *)
(*    with deciding. This is a reliable broadcast before deciding.       *)
(*  - If the coordinator crashes, undecided participants run a           *)
(*    termination protocol, which makes the protocol non-blocking.       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS participants,   \* set of participant identifiers
          yes, no,        \* votes
          undecided, commit, abort,  \* decisions
          waiting,        \* coordinator has not yet got a vote
          notsent         \* message not (yet) sent

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

Decisions == {undecided, commit, abort}

TypeInvParticipant ==
  participant \in [participants ->
      [ vote     : {yes, no},
        alive    : BOOLEAN,
        faulty   : BOOLEAN,
        voteSent : BOOLEAN,
        decision : Decisions,
        forward  : [participants -> {notsent, undecided, commit, abort}] ]]

TypeInvCoordinator ==
  coordinator \in
      [ request   : [participants -> BOOLEAN],
        vote      : [participants -> {waiting, yes, no}],
        broadcast : [participants -> {notsent, commit, abort}],
        decision  : Decisions,
        alive     : BOOLEAN,
        faulty    : BOOLEAN ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

-----------------------------------------------------------------------------
(* Initial states: votes are chosen nondeterministically *)

InitParticipant ==
  participant \in [participants ->
      [ vote     : {yes, no},
        alive    : {TRUE},
        faulty   : {FALSE},
        voteSent : {FALSE},
        decision : {undecided},
        forward  : {[j \in participants |-> notsent]} ]]

InitCoordinator ==
  coordinator = [ request   |-> [i \in participants |-> FALSE],
                  vote      |-> [i \in participants |-> waiting],
                  broadcast |-> [i \in participants |-> notsent],
                  decision  |-> undecided,
                  alive     |-> TRUE,
                  faulty    |-> FALSE ]

InitNB == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
(* Coordinator actions *)

CRequest(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

CGetVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* Synchronous timeout: perfect detection of a crashed participant that never voted
CDetectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[i] = waiting
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

CDecideCommit ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A i \in participants : coordinator.vote[i] = yes
  /\ coordinator' = [coordinator EXCEPT !.decision = commit]
  /\ UNCHANGED participant

CDecideAbort ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \E i \in participants : coordinator.vote[i] = no
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

CBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ coordinator.broadcast[i] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

CFail ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
  /\ UNCHANGED participant

CoordProgress ==
  \/ \E i \in participants : CRequest(i) \/ CGetVote(i) \/ CDetectFault(i)
                              \/ CBroadcast(i)
  \/ CDecideCommit
  \/ CDecideAbort

-----------------------------------------------------------------------------
(* Participant actions *)

\* Deciding atomically relays the decision to all participants
Decide(i, d) ==
  participant' = [participant EXCEPT
                    ![i].decision = d,
                    ![i].forward  = [j \in participants |-> d]]

PSendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* Unilateral abort is permitted for a participant that votes no
PAbortOnNo(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].vote = no
  /\ Decide(i, abort)
  /\ UNCHANGED coordinator

\* Receive the coordinator's decision. This is not allowed once in termination.
PReceiveDecision(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].forward[i] = notsent
  /\ coordinator.broadcast[i] # notsent
  /\ Decide(i, coordinator.broadcast[i])
  /\ UNCHANGED coordinator

\* Adopt a decision relayed by another participant
PReceiveForward(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ \E j \in participants :
        /\ participant[j].forward[i] \in {commit, abort}
        /\ Decide(i, participant[j].forward[i])
  /\ UNCHANGED coordinator

\* Termination protocol: the coordinator crash is detected (synchronous
\* timeout), and the participant announces that it is undecided.
PStartTermination(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.faulty
  /\ participant[i].forward[i] = notsent
  /\ participant' = [participant EXCEPT
                       ![i].forward = [j \in participants |-> undecided]]
  /\ UNCHANGED coordinator

\* Every live participant reported. No one relayed a decision, so abort.
PTerminationAbort(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.faulty
  /\ participant[i].forward[i] = undecided
  /\ \A j \in participants :
        /\ participant[j].forward[i] \notin {commit, abort}
        /\ participant[j].alive => participant[j].forward[i] # notsent
  /\ Decide(i, abort)
  /\ UNCHANGED coordinator

PFail(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

PartProgress(i) ==
  \/ PSendVote(i)
  \/ PAbortOnNo(i)
  \/ PReceiveDecision(i)
  \/ PReceiveForward(i)
  \/ PStartTermination(i)
  \/ PTerminationAbort(i)

-----------------------------------------------------------------------------

NextNB ==
  \/ CoordProgress
  \/ CFail
  \/ \E i \in participants : PartProgress(i) \/ PFail(i)

FairnessNB ==
  /\ WF_vars(CoordProgress)
  /\ \A i \in participants : WF_vars(PartProgress(i))

SpecNB == InitNB /\ [][NextNB]_vars /\ FairnessNB

-----------------------------------------------------------------------------
(* Properties *)

\* AC1 (agreement): no two participants decide differently
AC1 == [] \A i, j \in participants :
          ~ (participant[i].decision = commit /\ participant[j].decision = abort)

\* AC2 (validity): commit only if every participant voted yes
AC2 == [] ((\E i \in participants : participant[i].decision = commit)
             => (\A j \in participants : participant[j].vote = yes))

\* AC3_1: abort only if someone voted no, or a failure occurred
AC3_1 == [] ((\E i \in participants : participant[i].decision = abort)
               => \/ \E j \in participants : participant[j].vote = no
                  \/ \E j \in participants : participant[j].faulty
                  \/ coordinator.faulty)

\* AC3_2: if everyone votes yes and no failure ever occurs, everyone commits
AC3_2 == ( /\ \A i \in participants : participant[i].vote = yes
           /\ [] ( ~coordinator.faulty
                   /\ \A i \in participants : ~participant[i].faulty ) )
         => <> (\A i \in participants : participant[i].decision = commit)

\* AC4_alt (decision permanence): decisions never change once made
AC4_alt == [][ \A i \in participants :
                 /\ (participant[i].decision = commit => participant'[i].decision = commit)
                 /\ (participant[i].decision = abort  => participant'[i].decision = abort) ]_vars

\* AC5 (non-blocking termination): every live participant eventually decides
AC5 == <> (\A i \in participants :
             participant[i].alive => participant[i].decision # undecided)

=============================================================================
------------------------------ MODULE ACP ------------------------------
(***************************************************************************)
(* Atomic commitment protocol (two-phase commit style, with crash         *)
(* failures of the coordinator and the participants).                     *)
(*                                                                         *)
(* The coordinator requests votes from the participants. It collects the  *)
(* votes, decides, and broadcasts its decision. Participants that have     *)
(* decided forward their decision to the other participants. A commit     *)
(* is decided only if every participant voted yes. Abort is always a safe  *)
(* outcome. Decisions are irrevocable.                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants,   \* set of participant identifiers
          yes, no,        \* votes
          undecided, commit, abort, \* decisions
          waiting,        \* coordinator has not yet received a vote
          notsent         \* a decision has not been forwarded

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

Decisions == {undecided, commit, abort}

---------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
  /\ participant \in [participants ->
        [ vote     : {yes, no},
          alive    : BOOLEAN,
          decision : Decisions,
          voteSent : BOOLEAN,
          forward  : [participants -> {notsent, commit, abort}] ]]
  /\ coordinator \in
        [ request   : [participants -> BOOLEAN],
          vote      : [participants -> {waiting, yes, no}],
          alive     : BOOLEAN,
          decision  : Decisions,
          broadcast : [participants -> BOOLEAN] ]

---------------------------------------------------------------------------
(* Initial state: every participant has (nondeterministically) chosen its *)
(* vote; nobody has decided yet.                                           *)

Init ==
  /\ participant \in [participants ->
        [ vote     : {yes, no},
          alive    : {TRUE},
          decision : {undecided},
          voteSent : {FALSE},
          forward  : {[j \in participants |-> notsent]} ]]
  /\ coordinator =
        [ request   |-> [i \in participants |-> FALSE],
          vote      |-> [i \in participants |-> waiting],
          alive     |-> TRUE,
          decision  |-> undecided,
          broadcast |-> [i \in participants |-> FALSE] ]

---------------------------------------------------------------------------
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

\* Coordinator detects that a participant crashed before sending its vote.
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
  /\ ~coordinator.broadcast[i]
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
  /\ UNCHANGED participant

CDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

---------------------------------------------------------------------------
(* Participant actions *)

PSendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* A participant that votes no may unilaterally abort.
PAbortOnNo(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* The coordinator died before requesting this participant's vote.
PAbortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

PDecideOnBroadcast(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i]
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
  /\ UNCHANGED coordinator

PDecideOnForward(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ \E j \in participants :
        /\ participant[j].forward[i] # notsent
        /\ participant' = [participant EXCEPT
                              ![i].decision = participant[j].forward[i]]
  /\ UNCHANGED coordinator

PForward(i, j) ==
  /\ participant[i].alive
  /\ participant[i].decision # undecided
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT
                        ![i].forward[j] = participant[i].decision]
  /\ UNCHANGED coordinator

PDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------

Coord ==
  \/ \E i \in participants :
        CRequest(i) \/ CGetVote(i) \/ CDetectFault(i) \/ CBroadcast(i)
  \/ CDecideCommit
  \/ CDecideAbort

Parts ==
  \E i \in participants :
     \/ PSendVote(i)
     \/ PAbortOnNo(i)
     \/ PAbortOnTimeout(i)
     \/ PDecideOnBroadcast(i)
     \/ PDecideOnForward(i)
     \/ \E j \in participants : PForward(i, j)

Failures ==
  \/ CDie
  \/ \E i \in participants : PDie(i)

Next == Coord \/ Parts \/ Failures

Fairness ==
  /\ \A i \in participants :
        /\ WF_vars(CRequest(i))
        /\ WF_vars(CGetVote(i))
        /\ WF_vars(CDetectFault(i))
        /\ WF_vars(CBroadcast(i))
        /\ WF_vars(PSendVote(i))
        /\ WF_vars(PAbortOnTimeout(i))
        /\ WF_vars(PDecideOnBroadcast(i))
        /\ WF_vars(PDecideOnForward(i))
        /\ \A j \in participants : WF_vars(PForward(i, j))
  /\ WF_vars(CDecideCommit)
  /\ WF_vars(CDecideAbort)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Correctness properties *)

\* Agreement: no participant commits while another aborts.
AC1 ==
  \A i, j \in participants :
     ~ (participant[i].decision = commit /\ participant[j].decision = abort)

\* Justification: commit only if all participants voted yes.
AC2 ==
  (\E i \in participants : participant[i].decision = commit)
     => \A j \in participants : participant[j].vote = yes

\* The coordinator also only commits when justified.
CoordJustified ==
  coordinator.decision = commit => \A j \in participants : participant[j].vote = yes

\* Coordinator and participants agree.
CoordAgreement ==
  \A i \in participants :
     /\ (participant[i].decision = commit => coordinator.decision # abort)
     /\ (participant[i].decision = abort /\ coordinator.decision = commit)
           => FALSE

\* Irrevocability of decisions.
AC4 ==
  [][\A i \in participants :
        /\ participant[i].decision = commit => participant'[i].decision = commit
        /\ participant[i].decision = abort  => participant'[i].decision = abort]_vars

Safety == TypeOK /\ AC1 /\ AC2 /\ CoordJustified

\* Termination (holds when the coordinator does not fail before deciding).
AC3 ==
  <>[] (coordinator.alive =>
          \A i \in participants :
             participant[i].alive => participant[i].decision # undecided)

\* Symmetry among participants for state-space reduction.
Perms == Permutations(participants)

=============================================================================
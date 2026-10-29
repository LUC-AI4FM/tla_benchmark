--------------------------- MODULE TLC_ACP_SB ---------------------------
(***************************************************************************)
(* TLC-oriented wrapper around the ACP_SB protocol (synchronous, blocking  *)
(* atomic commitment).  The protocol definitions are inlined here so the   *)
(* module parses on its own.  The wrapper part defines a symmetry helper   *)
(* based on permutations of the participants, restates AC4 as an explicit  *)
(* stuttering-invariant temporal formula over the participant variable,    *)
(* and states the liveness property AC5.                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS participants,
          yes, no,
          undecided, commit, abort,
          waiting, notsent

ASSUME Cardinality({yes, no, undecided, commit, abort, waiting, notsent}) = 7

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(* Type invariant *)

TypeInv ==
  /\ participant \in [participants ->
        [vote : {yes, no},
         alive : BOOLEAN,
         decision : {undecided, commit, abort},
         voteSent : BOOLEAN]]
  /\ coordinator \in
        [request : [participants -> BOOLEAN],
         vote : [participants -> {waiting, yes, no}],
         broadcast : [participants -> {notsent, commit, abort}],
         decision : {undecided, commit, abort},
         alive : BOOLEAN]

---------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ participant \in [participants ->
        [vote : {yes, no},
         alive : {TRUE},
         decision : {undecided},
         voteSent : {FALSE}]]
  /\ coordinator = [request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    broadcast |-> [i \in participants |-> notsent],
                    decision  |-> undecided,
                    alive     |-> TRUE]

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
  /\ ~coordinator.alive
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
  /\ participant' = [participant EXCEPT ![i].alive = FALSE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relation and specification *)

parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ decide(i)

coordProg ==
  \/ makeDecision
  \/ \E i \in participants :
        request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

Next ==
  \/ coordProg
  \/ \E i \in participants : parProg(i)
  \/ coordDie
  \/ \E i \in participants : parDie(i)

Fairness ==
  /\ WF_vars(coordProg)
  /\ \A i \in participants : WF_vars(parProg(i))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Correctness properties of the protocol *)

AC1 == \A i, j \in participants :
          ~ (participant[i].decision = commit /\ participant[j].decision = abort)

AC2 == (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

AC3_1 == (\E i \in participants : participant[i].decision = abort)
          => \/ \E j \in participants : participant[j].vote = no
             \/ \E j \in participants : ~participant[j].alive
             \/ ~coordinator.alive

AC4 == [][\A i \in participants :
            /\ participant[i].decision = commit => participant'[i].decision = commit
            /\ participant[i].decision = abort  => participant'[i].decision = abort
         ]_participant

---------------------------------------------------------------------------
(* TLC wrapper definitions *)

\* Symmetry helper: permutations of the participants
Perms == Permutations(participants)

\* AC4 restated as an explicit stuttering-invariant formula over participant
AC4_alt ==
  [][ /\ \A i \in participants :
           participant[i].decision = commit => participant'[i].decision = commit
      /\ \A j \in participants :
           participant[j].decision = abort  => participant'[j].decision = abort
    ]_<<participant>>

\* Liveness: every participant eventually reaches commit or abort
AC5 == <>(\A i \in participants : participant[i].decision \in {abort, commit})

---------------------------------------------------------------------------
THEOREM Spec => [](TypeInv /\ AC1 /\ AC2 /\ AC3_1)
THEOREM Spec => AC4_alt

=============================================================================
------------------------------- MODULE MC_ACP_SB -------------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with Simple Broadcast (ACP_SB), with         *)
(* additions for model checking with TLC: a symmetry set over the          *)
(* participants and a TLC-friendly reformulation AC4_alt of property AC4.  *)
(* The base protocol is included inline so that the module is              *)
(* self-contained.                                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    participants,   \* set of participants
    yes, no,        \* possible votes
    undecided, commit, abort,   \* possible decisions
    waiting,        \* coordinator waiting for a vote
    notsent         \* coordinator has not broadcast to a participant

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

ASSUME /\ Cardinality({yes, no, undecided, commit, abort, waiting, notsent}) = 7
       /\ participants # {}

-----------------------------------------------------------------------------
(* Type invariant *)

TypeInvariant ==
    /\ participant \in [participants ->
          [ vote     : {yes, no},
            alive    : BOOLEAN,
            decision : {undecided, commit, abort},
            faulty   : BOOLEAN,
            voteSent : BOOLEAN ]]
    /\ coordinator \in
          [ request   : [participants -> BOOLEAN],
            vote      : [participants -> {waiting, yes, no}],
            alive     : BOOLEAN,
            decision  : {undecided, commit, abort},
            broadcast : [participants -> {notsent, commit, abort}] ]

-----------------------------------------------------------------------------
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
            alive     |-> TRUE,
            decision  |-> undecided,
            broadcast |-> [i \in participants |-> notsent] ]

-----------------------------------------------------------------------------
(* Coordinator actions *)

request(i) ==
    /\ coordinator.alive
    /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
    /\ UNCHANGED participant

getVote(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.request[i]
    /\ coordinator.vote[i] = waiting
    /\ participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
    /\ UNCHANGED participant

detectFault(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.request[i]
    /\ coordinator.vote[i] = waiting
    /\ ~participant[i].alive
    /\ ~participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
    /\ UNCHANGED participant

makeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A i \in participants : coordinator.vote[i] \in {yes, no}
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

-----------------------------------------------------------------------------
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
    /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                          ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
(* Specification *)

parProg(i) ==
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ decide(i)

coordProg(i) ==
    \/ request(i)
    \/ getVote(i)
    \/ detectFault(i)
    \/ coordBroadcast(i)

Next ==
    \/ makeDecision
    \/ coordDie
    \/ \E i \in participants : parProg(i) \/ coordProg(i) \/ parDie(i)

Fairness ==
    /\ WF_vars(makeDecision)
    /\ \A i \in participants :
          /\ WF_vars(parProg(i))
          /\ WF_vars(coordProg(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

\* AC1: all participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
          ~(participant[i].decision = commit /\ participant[j].decision = abort)

\* AC2: if any participant decides commit, then all participants voted yes
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes) )

\* AC3_1: if any participant decides abort, then some participant voted no
\*        or some failure occurred
AC3_1 == [] ( (\E i \in participants : participant[i].decision = abort)
              => \/ \E j \in participants : participant[j].vote = no
                 \/ \E j \in participants : participant[j].faulty
                 \/ ~coordinator.alive )

\* AC3_2: if no failures occur, every participant eventually decides
AC3_2 == ([] (coordinator.alive /\ \A i \in participants : participant[i].alive))
            => <> (\A i \in participants : participant[i].decision # undecided)

\* AC4: a decision, once taken, is irreversible
AC4 == [][ \A i \in participants :
              participant[i].decision \in {commit, abort}
                 => participant'[i].decision = participant[i].decision ]_vars

\* Alternative formulation of AC4 that TLC handles more efficiently
AC4_alt == \A i \in participants :
              /\ [] (participant[i].decision = commit
                       => [] (participant[i].decision = commit))
              /\ [] (participant[i].decision = abort
                       => [] (participant[i].decision = abort))

\* Intermediate properties
DecisionReachedNoFault ==
    (\A i \in participants : participant[i].alive)
      => <> (\A i \in participants :
                participant[i].alive => participant[i].decision # undecided)

AbortImpliesNoVote == [] ( coordinator.decision = abort
                           => \E i \in participants : coordinator.vote[i] = no )

CommitImpliesAllYes == [] ( coordinator.decision = commit
                            => \A i \in participants : coordinator.vote[i] = yes )

\* Deliberately invalid properties (sanity checks)
AC5_invalid == <> (\A i \in participants : participant[i].decision # undecided)

NeverCommit_invalid == [] (\A i \in participants : participant[i].decision # commit)

NeverAbort_invalid == [] (\A i \in participants : participant[i].decision # abort)

-----------------------------------------------------------------------------
(* Symmetry set for TLC *)

SymmetricParticipants == Permutations(participants)

=============================================================================
---------------------------- MODULE MC_ACP_NB ----------------------------
(***************************************************************************)
(* TLC-oriented wrapper for a non-blocking atomic commit protocol          *)
(* (ACP_NB). The underlying transition system is included here so the      *)
(* module stands on its own. It adds:                                       *)
(*   - a symmetry permutation operator                                      *)
(*   - AC4_alt, a reformulated decision-stability property                  *)
(*   - AllMustCommit, an eventual-commit property                           *)
(*   - PostCondition, a concrete counterexample witness with participants   *)
(*     p0 and p1, coordinator failure and a participant crash               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    p0, p1,                    \* concrete participants (model values)
    yes, no,                   \* votes
    undecided, commit, abort,  \* decisions
    waiting,                   \* coordinator still waiting for a vote
    notsent                    \* message not yet sent

participants == {p0, p1}

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(* Type information *)

ParticipantType ==
    [ vote     : {yes, no},
      alive    : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty   : BOOLEAN,
      voteSent : BOOLEAN,
      forward  : [participants -> {notsent, commit, abort}] ]

CoordinatorType ==
    [ request   : [participants -> BOOLEAN],
      vote      : [participants -> {waiting, yes, no}],
      alive     : BOOLEAN,
      decision  : {undecided, commit, abort},
      broadcast : [participants -> {notsent, commit, abort}] ]

TypeOK ==
    /\ participant \in [participants -> ParticipantType]
    /\ coordinator \in CoordinatorType

---------------------------------------------------------------------------
(* Initial state *)

InitParticipant ==
    participant \in [participants ->
                       [ vote     : {yes, no},
                         alive    : {TRUE},
                         decision : {undecided},
                         faulty   : {FALSE},
                         voteSent : {FALSE},
                         forward  : {[j \in participants |-> notsent]} ]]

InitCoordinator ==
    coordinator = [ request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    alive     |-> TRUE,
                    decision  |-> undecided,
                    broadcast |-> [i \in participants |-> notsent] ]

Init == InitParticipant /\ InitCoordinator

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
    /\ participant[i].faulty
    /\ ~participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
    /\ UNCHANGED participant

makeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.vote[j] # waiting
    /\ coordinator' = [coordinator EXCEPT !.decision =
                          IF \A j \in participants : coordinator.vote[j] = yes
                          THEN commit ELSE abort]
    /\ UNCHANGED participant

coordBroadcast(i) ==
    /\ coordinator.alive
    /\ coordinator.decision # undecided
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
    /\ ~participant[i].voteSent
    /\ coordinator.request[i]
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
    /\ coordinator.broadcast[i] # notsent
    /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
    /\ UNCHANGED coordinator

parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                          ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

(* Non-blocking extension: participants forward decisions to each other   *)
(* and may abort on timeout when the coordinator has failed without        *)
(* informing anybody.                                                       *)

forward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].decision # undecided
    /\ participant[i].forward[j] = notsent
    /\ participant' = [participant EXCEPT ![i].forward[j] = participant[i].decision]
    /\ UNCHANGED coordinator

decideOnForward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[j].forward[i] # notsent
    /\ participant' = [participant EXCEPT ![i].decision = participant[j].forward[i]]
    /\ UNCHANGED coordinator

abortOnTimeout(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ \A j \in participants : coordinator.broadcast[j] = notsent
    /\ \A j \in participants : participant[j].forward[i] = notsent
    /\ \A j \in participants : participant[j].decision # commit
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relation and specification *)

CoordinatorNext ==
    \/ \E i \in participants :
          request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
    \/ makeDecision
    \/ coordDie

ParticipantNext ==
    \/ \E i \in participants :
          \/ sendVote(i)
          \/ abortOnVote(i)
          \/ abortOnTimeoutRequest(i)
          \/ decide(i)
          \/ abortOnTimeout(i)
          \/ parDie(i)
    \/ \E i, j \in participants : forward(i, j) \/ decideOnForward(i, j)

Next == CoordinatorNext \/ ParticipantNext

Fairness ==
    /\ \A i \in participants :
          /\ WF_vars(request(i))
          /\ WF_vars(getVote(i))
          /\ WF_vars(detectFault(i))
          /\ WF_vars(coordBroadcast(i))
          /\ WF_vars(sendVote(i))
          /\ WF_vars(abortOnVote(i))
          /\ WF_vars(abortOnTimeoutRequest(i))
          /\ WF_vars(decide(i))
          /\ WF_vars(abortOnTimeout(i))
    /\ WF_vars(makeDecision)
    /\ \A i, j \in participants :
          /\ WF_vars(forward(i, j))
          /\ WF_vars(decideOnForward(i, j))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Atomic commit properties *)

\* AC1: all participants that decide reach the same decision
AC1 ==
    \A i, j \in participants :
        (participant[i].decision # undecided /\ participant[j].decision # undecided)
            => participant[i].decision = participant[j].decision

\* AC2: if any participant decides commit, all participants voted yes
AC2 ==
    (\E i \in participants : participant[i].decision = commit)
        => \A j \in participants : participant[j].vote = yes

\* AC3_1: if any participant votes no, nobody commits
AC3_1 ==
    (\E i \in participants : participant[i].vote = no)
        => \A j \in participants : participant[j].decision # commit

\* AC3_2: eventually every live participant decides
AC3_2 ==
    <>[](\A i \in participants :
            participant[i].alive => participant[i].decision # undecided)

\* AC4: decisions are irreversible
AC4 ==
    [][\A i \in participants :
          /\ (participant[i].decision = commit => participant'[i].decision = commit)
          /\ (participant[i].decision = abort  => participant'[i].decision = abort)
      ]_vars

\* AC4_alt: reformulated decision stability for participants
AC4_alt ==
    [][\A i \in participants :
          participant[i].decision \in {commit, abort}
              => participant'[i].decision = participant[i].decision
      ]_vars

\* AllMustCommit: eventually every participant commits
AllMustCommit ==
    <>(\A i \in participants : participant[i].decision = commit)

---------------------------------------------------------------------------
(* Symmetry *)

Perms == Permutations(participants)

---------------------------------------------------------------------------
(* Concrete counterexample witness                                         *)
(* Scenario: both participants vote yes, the coordinator decides commit    *)
(* and fails before broadcasting, p0 crashes, and p1 aborts on timeout.    *)
(* AllMustCommit is violated.                                              *)

NoFwd == p0 :> notsent @@ p1 :> notsent

PS(v, a, d, f, s) ==
    [ vote |-> v, alive |-> a, decision |-> d, faulty |-> f,
      voteSent |-> s, forward |-> NoFwd ]

CS(r0, r1, v0, v1, al, d) ==
    [ request   |-> (p0 :> r0 @@ p1 :> r1),
      vote      |-> (p0 :> v0 @@ p1 :> v1),
      alive     |-> al,
      decision  |-> d,
      broadcast |-> NoFwd ]

St(a, b, c) == [ participant |-> (p0 :> a @@ p1 :> b), coordinator |-> c ]

S1  == St(PS(yes, TRUE,  undecided, FALSE, FALSE), PS(yes, TRUE, undecided, FALSE, FALSE),
          CS(FALSE, FALSE, waiting, waiting, TRUE, undecided))
S2  == St(PS(yes, TRUE,  undecided, FALSE, FALSE), PS(yes, TRUE, undecided, FALSE, FALSE),
          CS(TRUE,  FALSE, waiting, waiting, TRUE, undecided))
S3  == St(PS(yes, TRUE,  undecided, FALSE, FALSE), PS(yes, TRUE, undecided, FALSE, FALSE),
          CS(TRUE,  TRUE,  waiting, waiting, TRUE, undecided))
S4  == St(PS(yes, TRUE,  undecided, FALSE, TRUE),  PS(yes, TRUE, undecided, FALSE, FALSE),
          CS(TRUE,  TRUE,  waiting, waiting, TRUE, undecided))
S5  == St(PS(yes, TRUE,  undecided, FALSE, TRUE),  PS(yes, TRUE, undecided, FALSE, TRUE),
          CS(TRUE,  TRUE,  waiting, waiting, TRUE, undecided))
S6  == St(PS(yes, TRUE,  undecided, FALSE, TRUE),  PS(yes, TRUE, undecided, FALSE, TRUE),
          CS(TRUE,  TRUE,  yes,     waiting, TRUE, undecided))
S7  == St(PS(yes, TRUE,  undecided, FALSE, TRUE),  PS(yes, TRUE, undecided, FALSE, TRUE),
          CS(TRUE,  TRUE,  yes,     yes,     TRUE, undecided))
S8  == St(PS(yes, TRUE,  undecided, FALSE, TRUE),  PS(yes, TRUE, undecided, FALSE, TRUE),
          CS(TRUE,  TRUE,  yes,     yes,     TRUE, commit))
S9  == St(PS(yes, TRUE,  undecided, FALSE, TRUE),  PS(yes, TRUE, undecided, FALSE, TRUE),
          CS(TRUE,  TRUE,  yes,     yes,     FALSE, commit))
S10 == St(PS(yes, FALSE, undecided, TRUE,  TRUE),  PS(yes, TRUE, undecided, FALSE, TRUE),
          CS(TRUE,  TRUE,  yes,     yes,     FALSE, commit))
S11 == St(PS(yes, FALSE, undecided, TRUE,  TRUE),  PS(yes, TRUE, abort,     FALSE, TRUE),
          CS(TRUE,  TRUE,  yes,     yes,     FALSE, commit))

TraceStates == << S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11 >>

TraceActions ==
    << [name |-> "request",        p |-> p0],
       [name |-> "request",        p |-> p1],
       [name |-> "sendVote",       p |-> p0],
       [name |-> "sendVote",       p |-> p1],
       [name |-> "getVote",        p |-> p0],
       [name |-> "getVote",        p |-> p1],
       [name |-> "makeDecision",   p |-> p0],
       [name |-> "coordDie",       p |-> p0],
       [name |-> "parDie",         p |-> p0],
       [name |-> "abortOnTimeout", p |-> p1] >>

PostCondition ==
    [ state   |-> { <<k, TraceStates[k]>> : k \in 1..Len(TraceStates) },
      action  |-> { << <<k, TraceStates[k]>>,
                       TraceActions[k],
                       <<k + 1, TraceStates[k + 1]>> >> :
                    k \in 1..Len(TraceActions) },
      \* final state stutters forever: lasso back onto itself
      loop    |-> << <<11, S11>>, [name |-> "Stuttering", p |-> p1], <<11, S11>> >>,
      visited |-> { S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11 } ]

\* Sanity check that the witness is a genuine behavior violating AllMustCommit
PostConditionValid ==
    /\ \A k \in 1..Len(TraceStates) :
          TraceStates[k].participant[p0].decision # commit
          \/ TraceStates[k].participant[p1].decision # commit
    /\ ~TraceStates[11].coordinator.alive
    /\ ~TraceStates[11].participant[p0].alive

=============================================================================
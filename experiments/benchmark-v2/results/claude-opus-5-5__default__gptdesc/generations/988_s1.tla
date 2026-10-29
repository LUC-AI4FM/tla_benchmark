---------------------------- MODULE ACP_NB_TLC ----------------------------
(***************************************************************************)
(* TLC-oriented wrapper around a non-blocking atomic commit protocol.      *)
(* The underlying ACP_NB transition system is inlined here so that the     *)
(* module is self-contained. On top of it the module adds:                 *)
(*   - a symmetry permutation operator for TLC,                            *)
(*   - AC4_alt, a reformulation of decision stability for participants,    *)
(*   - AllMustCommit, an eventual-commit property, and                     *)
(*   - PostCondition, a TLC value encoding a concrete counterexample       *)
(*     trace and its visited states. The scenario has two participants     *)
(*     p0 and p1, a coordinator failure and a participant crash.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS participants, p0, p1

ASSUME /\ p0 \in participants
       /\ p1 \in participants
       /\ p0 # p1

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

Votes      == {"yes", "no"}
Decisions  == {"undecided", "commit", "abort"}
Forwards   == {"notsent", "undecided", "commit", "abort"}

-----------------------------------------------------------------------------
(* Type invariant *)

TypeInv ==
  /\ participant \in [participants ->
        [vote     : Votes,
         alive    : BOOLEAN,
         decision : Decisions,
         faulty   : BOOLEAN,
         voteSent : BOOLEAN,
         forward  : [participants -> Forwards]]]
  /\ coordinator \in
        [request   : [participants -> BOOLEAN],
         vote      : [participants -> {"waiting", "yes", "no"}],
         alive     : BOOLEAN,
         decision  : Decisions,
         broadcast : [participants -> BOOLEAN]]

-----------------------------------------------------------------------------
(* Initial state *)

InitParticipant ==
  participant \in [participants ->
        [vote     : Votes,
         alive    : {TRUE},
         decision : {"undecided"},
         faulty   : {FALSE},
         voteSent : {FALSE},
         forward  : {[j \in participants |-> "notsent"]}]]

InitCoordinator ==
  coordinator = [request   |-> [i \in participants |-> FALSE],
                 vote      |-> [i \in participants |-> "waiting"],
                 alive     |-> TRUE,
                 decision  |-> "undecided",
                 broadcast |-> [i \in participants |-> FALSE]]

Init == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
(* Coordinator actions *)

Request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

GetVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ participant[i].voteSent
  /\ coordinator.vote[i] = "waiting"
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

DetectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ ~participant[i].alive
  /\ coordinator.vote[i] = "waiting"
  /\ coordinator' = [coordinator EXCEPT !.decision = "abort"]
  /\ UNCHANGED participant

MakeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ \A i \in participants : coordinator.vote[i] # "waiting"
  /\ coordinator' = [coordinator EXCEPT !.decision =
        IF \A i \in participants : coordinator.vote[i] = "yes"
          THEN "commit" ELSE "abort"]
  /\ UNCHANGED participant

CoordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # "undecided"
  /\ ~coordinator.broadcast[i]
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
  /\ UNCHANGED participant

CoordFail ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

-----------------------------------------------------------------------------
(* Participant actions *)

SendVote(i) ==
  /\ participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

AbortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ participant[i].voteSent
  /\ participant[i].vote = "no"
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

AbortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

Decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ coordinator.broadcast[i]
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
  /\ UNCHANGED coordinator

ParFail(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE]
  /\ UNCHANGED coordinator

ParDetectFault(i) ==
  /\ participant[i].alive
  /\ ~participant[i].faulty
  /\ participant[i].decision = "undecided"
  /\ participant[i].voteSent
  /\ ~coordinator.alive
  /\ participant' = [participant EXCEPT ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

Forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].forward[j] = "notsent"
  /\ (participant[i].decision # "undecided" \/ participant[i].faulty)
  /\ participant' = [participant EXCEPT
                       ![i].forward[j] = participant[i].decision]
  /\ UNCHANGED coordinator

DecideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ participant[j].forward[i] \in {"commit", "abort"}
  /\ participant' = [participant EXCEPT
                       ![i].decision = participant[j].forward[i]]
  /\ UNCHANGED coordinator

AbortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].faulty
  /\ participant[i].decision = "undecided"
  /\ \A j \in participants \ {i} :
        participant[j].alive => participant[j].forward[i] = "undecided"
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

CoordProgress ==
  \/ \E i \in participants :
        Request(i) \/ GetVote(i) \/ DetectFault(i) \/ CoordBroadcast(i)
  \/ MakeDecision

ParProgress(i) ==
  \/ SendVote(i)
  \/ AbortOnVote(i)
  \/ AbortOnTimeoutRequest(i)
  \/ Decide(i)
  \/ ParDetectFault(i)
  \/ AbortOnTimeout(i)
  \/ \E j \in participants : Forward(i, j) \/ DecideOnForward(i, j)

Next ==
  \/ CoordProgress
  \/ CoordFail
  \/ \E i \in participants : ParProgress(i) \/ ParFail(i)

Fairness ==
  /\ WF_vars(CoordProgress)
  /\ \A i \in participants : WF_vars(ParProgress(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties of the underlying protocol *)

AC1 ==
  \A i, j \in participants :
     /\ participant[i].decision # "undecided"
     /\ participant[j].decision # "undecided"
     => participant[i].decision = participant[j].decision

AC2 ==
  (\E i \in participants : participant[i].decision = "commit")
     => \A j \in participants : participant[j].vote = "yes"

AC3_2 ==
  <>[](\A i \in participants :
          participant[i].alive => participant[i].decision # "undecided")

AC4 ==
  [][\A i \in participants :
       participant[i].decision # "undecided"
          => participant'[i].decision = participant[i].decision]_vars

-----------------------------------------------------------------------------
(* TLC wrapper definitions *)

\* Symmetry permutation operator for TLC
Perms == Permutations(participants)

\* Alternative formulation of decision stability for participants
AC4_alt ==
  \A i \in participants :
     /\ [](participant[i].decision = "commit"
             => [](participant[i].decision = "commit"))
     /\ [](participant[i].decision = "abort"
             => [](participant[i].decision = "abort"))

\* Eventually every participant commits
AllMustCommit ==
  <>(\A i \in participants : participant[i].decision = "commit")

-----------------------------------------------------------------------------
(* Concrete counterexample witness (two participants p0 and p1)            *)

PState(v, a, d, f, s, f0, f1) ==
  [vote |-> v, alive |-> a, decision |-> d, faulty |-> f,
   voteSent |-> s, forward |-> (p0 :> f0 @@ p1 :> f1)]

CState(r0, r1, v0, v1, a, d, b0, b1) ==
  [request   |-> (p0 :> r0 @@ p1 :> r1),
   vote      |-> (p0 :> v0 @@ p1 :> v1),
   alive     |-> a,
   decision  |-> d,
   broadcast |-> (p0 :> b0 @@ p1 :> b1)]

TState(pp0, pp1, c) ==
  [participant |-> (p0 :> pp0 @@ p1 :> pp1), coordinator |-> c]

N == "notsent"
U == "undecided"

CounterexampleTrace ==
  << \* 1: Init
     TState(PState("yes", TRUE, U, FALSE, FALSE, N, N),
            PState("yes", TRUE, U, FALSE, FALSE, N, N),
            CState(FALSE, FALSE, "waiting", "waiting", TRUE, U, FALSE, FALSE)),
     \* 2: Request(p0)
     TState(PState("yes", TRUE, U, FALSE, FALSE, N, N),
            PState("yes", TRUE, U, FALSE, FALSE, N, N),
            CState(TRUE, FALSE, "waiting", "waiting", TRUE, U, FALSE, FALSE)),
     \* 3: Request(p1)
     TState(PState("yes", TRUE, U, FALSE, FALSE, N, N),
            PState("yes", TRUE, U, FALSE, FALSE, N, N),
            CState(TRUE, TRUE, "waiting", "waiting", TRUE, U, FALSE, FALSE)),
     \* 4: SendVote(p0)
     TState(PState("yes", TRUE, U, FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, FALSE, N, N),
            CState(TRUE, TRUE, "waiting", "waiting", TRUE, U, FALSE, FALSE)),
     \* 5: SendVote(p1)
     TState(PState("yes", TRUE, U, FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, TRUE, N, N),
            CState(TRUE, TRUE, "waiting", "waiting", TRUE, U, FALSE, FALSE)),
     \* 6: GetVote(p0)
     TState(PState("yes", TRUE, U, FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "waiting", TRUE, U, FALSE, FALSE)),
     \* 7: GetVote(p1)
     TState(PState("yes", TRUE, U, FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "yes", TRUE, U, FALSE, FALSE)),
     \* 8: MakeDecision
     TState(PState("yes", TRUE, U, FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "yes", TRUE, "commit", FALSE, FALSE)),
     \* 9: CoordBroadcast(p0)
     TState(PState("yes", TRUE, U, FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "yes", TRUE, "commit", TRUE, FALSE)),
     \* 10: Decide(p0)
     TState(PState("yes", TRUE, "commit", FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "yes", TRUE, "commit", TRUE, FALSE)),
     \* 11: ParFail(p0)
     TState(PState("yes", FALSE, "commit", FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "yes", TRUE, "commit", TRUE, FALSE)),
     \* 12: CoordFail
     TState(PState("yes", FALSE, "commit", FALSE, TRUE, N, N),
            PState("yes", TRUE, U, FALSE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "yes", FALSE, "commit", TRUE, FALSE)),
     \* 13: ParDetectFault(p1)
     TState(PState("yes", FALSE, "commit", FALSE, TRUE, N, N),
            PState("yes", TRUE, U, TRUE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "yes", FALSE, "commit", TRUE, FALSE)),
     \* 14: AbortOnTimeout(p1)
     TState(PState("yes", FALSE, "commit", FALSE, TRUE, N, N),
            PState("yes", TRUE, "abort", TRUE, TRUE, N, N),
            CState(TRUE, TRUE, "yes", "yes", FALSE, "commit", TRUE, FALSE))
  >>

CounterexampleActions ==
  << "Init", "Request(p0)", "Request(p1)", "SendVote(p0)", "SendVote(p1)",
     "GetVote(p0)", "GetVote(p1)", "MakeDecision", "CoordBroadcast(p0)",
     "Decide(p0)", "ParFail(p0)", "CoordFail", "ParDetectFault(p1)",
     "AbortOnTimeout(p1)" >>

PostCondition ==
  [ property |-> "AllMustCommit",
    trace    |-> [k \in DOMAIN CounterexampleTrace |->
                    [action |-> CounterexampleActions[k],
                     state  |-> CounterexampleTrace[k]]],
    visited  |-> {CounterexampleTrace[k] : k \in DOMAIN CounterexampleTrace},
    length   |-> Len(CounterexampleTrace) ]

\* Check that the final state of the witness violates the expected goals
PostConditionCheck ==
  LET last == CounterexampleTrace[Len(CounterexampleTrace)]
  IN  /\ last.participant[p0].decision = "commit"
      /\ last.participant[p1].decision = "abort"
      /\ ~last.coordinator.alive
      /\ ~last.participant[p0].alive

=============================================================================
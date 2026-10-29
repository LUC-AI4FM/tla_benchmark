------------------------------- MODULE MC_ACP_NB -------------------------------
(***************************************************************************)
(* TLC-oriented wrapper around a non-blocking atomic commit protocol       *)
(* (ACP_NB). The transition system is included here so the module is       *)
(* self-contained. On top of it the module defines:                        *)
(*   - Perms: the symmetry permutations of the participants,               *)
(*   - AC4_alt: a reformulation of decision stability for participants,    *)
(*   - AllMustCommit: an eventual-commit property (expected to fail),      *)
(*   - PostCondition: a concrete witness of a counterexample trace with    *)
(*     two participants p0 and p1, coordinator failure and participant     *)
(*     crashes.                                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS participants

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

\* Message / decision values
yes       == "yes"
no        == "no"
undecided == "undecided"
commit    == "commit"
abort     == "abort"
waiting   == "waiting"
notsent   == "notsent"

-----------------------------------------------------------------------------
(* Type invariant *)

TypeInv ==
  /\ participant \in [participants ->
        [vote     : {yes, no},
         alive    : BOOLEAN,
         decision : {undecided, commit, abort},
         faulty   : BOOLEAN,
         voteSent : BOOLEAN,
         forward  : [participants -> {notsent, commit, abort}]]]
  /\ coordinator \in
        [request   : [participants -> BOOLEAN],
         vote      : [participants -> {waiting, yes, no}],
         alive     : BOOLEAN,
         decision  : {undecided, commit, abort},
         broadcast : [participants -> {notsent, commit, abort}]]

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ participant \in [participants ->
        [vote     : {yes, no},
         alive    : {TRUE},
         decision : {undecided},
         faulty   : {FALSE},
         voteSent : {FALSE},
         forward  : {[j \in participants |-> notsent]}]]
  /\ coordinator = [request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    alive     |-> TRUE,
                    decision  |-> undecided,
                    broadcast |-> [i \in participants |-> notsent]]

-----------------------------------------------------------------------------
(* Coordinator actions *)

request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

coordDecide ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \/ /\ \A i \in participants : coordinator.vote[i] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E i \in participants :
              \/ coordinator.vote[i] = no
              \/ /\ coordinator.vote[i] = waiting
                 /\ ~participant[i].alive
        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
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

-----------------------------------------------------------------------------
(* Participant actions *)

sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]

abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

receiveDecision(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i] # notsent
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

forward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision # undecided
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i].forward[j] = participant[i].decision]
  /\ UNCHANGED coordinator

decideOnForward(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ \E j \in participants :
        /\ participant[j].forward[i] # notsent
        /\ participant' = [participant EXCEPT ![i].decision = participant[j].forward[i]]
  /\ UNCHANGED coordinator

abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~coordinator.alive
  /\ coordinator.broadcast[i] = notsent
  /\ \A j \in participants : participant[j].forward[i] = notsent
  /\ \A j \in participants \ {i} : participant[j].decision = undecided
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

participantDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Coordinator ==
  \/ \E i \in participants : request(i) \/ coordBroadcast(i)
  \/ coordDecide
  \/ coordDie

Participant ==
  \E i \in participants :
     \/ sendVote(i)
     \/ abortOnVote(i)
     \/ receiveDecision(i)
     \/ decideOnForward(i)
     \/ abortOnTimeout(i)
     \/ participantDie(i)
     \/ \E j \in participants : forward(i, j)

Next == Coordinator \/ Participant

Fairness ==
  /\ WF_vars(coordDecide)
  /\ \A i \in participants :
        /\ WF_vars(request(i))
        /\ WF_vars(coordBroadcast(i))
        /\ WF_vars(sendVote(i))
        /\ WF_vars(abortOnVote(i))
        /\ WF_vars(receiveDecision(i))
        /\ WF_vars(decideOnForward(i))
        /\ WF_vars(abortOnTimeout(i))
        /\ \A j \in participants : WF_vars(forward(i, j))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties of the atomic commit protocol *)

\* AC1: all participants that decide reach the same decision
AC1 ==
  \A i, j \in participants :
     (participant[i].decision # undecided /\ participant[j].decision # undecided)
        => participant[i].decision = participant[j].decision

\* AC2: commit only if all participants voted yes
AC2 ==
  (\E i \in participants : participant[i].decision = commit)
     => \A j \in participants : participant[j].vote = yes

\* AC3: if some participant voted no, nobody commits
AC3_1 ==
  (\E i \in participants : participant[i].vote = no)
     => \A j \in participants : participant[j].decision # commit

\* AC4: decisions are irreversible
AC4 ==
  [][\A i \in participants :
        participant[i].decision # undecided
           => participant'[i].decision = participant[i].decision]_vars

\* AC5: non-blocking termination: every alive participant eventually decides
AC5 ==
  <>(\A i \in participants :
        participant[i].alive => participant[i].decision # undecided)

-----------------------------------------------------------------------------
(* TLC wrapper definitions *)

\* Symmetry permutations of the participants
Perms == Permutations(participants)

\* Alternative formulation of decision stability for participants
AC4_alt ==
  [][\A i \in participants :
        /\ (participant[i].decision = commit) => (participant'[i].decision = commit)
        /\ (participant[i].decision = abort)  => (participant'[i].decision = abort)]_vars

\* Eventually all participants commit (expected to be violated)
AllMustCommit ==
  <>(\A i \in participants : participant[i].decision = commit)

-----------------------------------------------------------------------------
(* Concrete counterexample witness: participants p0 and p1, coordinator    *)
(* decides commit, broadcasts to p0 only and crashes; p0 commits and       *)
(* crashes, then p1 crashes, so AllMustCommit can never hold.              *)

CexParts == {"p0", "p1"}

CexP(v, a, d, f, s) ==
  [vote |-> v, alive |-> a, decision |-> d, faulty |-> f, voteSent |-> s,
   forward |-> [j \in CexParts |-> notsent]]

CexC(r0, r1, v0, v1, d, b0, b1, a) ==
  [request   |-> ("p0" :> r0 @@ "p1" :> r1),
   vote      |-> ("p0" :> v0 @@ "p1" :> v1),
   alive     |-> a,
   decision  |-> d,
   broadcast |-> ("p0" :> b0 @@ "p1" :> b1)]

CexS(pp0, pp1, c) ==
  [participant |-> ("p0" :> pp0 @@ "p1" :> pp1), coordinator |-> c]

CexS1  == CexS(CexP(yes, TRUE, undecided, FALSE, FALSE),
               CexP(yes, TRUE, undecided, FALSE, FALSE),
               CexC(FALSE, FALSE, waiting, waiting, undecided, notsent, notsent, TRUE))
CexS2  == CexS(CexP(yes, TRUE, undecided, FALSE, FALSE),
               CexP(yes, TRUE, undecided, FALSE, FALSE),
               CexC(TRUE, FALSE, waiting, waiting, undecided, notsent, notsent, TRUE))
CexS3  == CexS(CexP(yes, TRUE, undecided, FALSE, FALSE),
               CexP(yes, TRUE, undecided, FALSE, FALSE),
               CexC(TRUE, TRUE, waiting, waiting, undecided, notsent, notsent, TRUE))
CexS4  == CexS(CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexP(yes, TRUE, undecided, FALSE, FALSE),
               CexC(TRUE, TRUE, yes, waiting, undecided, notsent, notsent, TRUE))
CexS5  == CexS(CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexC(TRUE, TRUE, yes, yes, undecided, notsent, notsent, TRUE))
CexS6  == CexS(CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexC(TRUE, TRUE, yes, yes, commit, notsent, notsent, TRUE))
CexS7  == CexS(CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexC(TRUE, TRUE, yes, yes, commit, commit, notsent, TRUE))
CexS8  == CexS(CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexC(TRUE, TRUE, yes, yes, commit, commit, notsent, FALSE))
CexS9  == CexS(CexP(yes, TRUE, commit, FALSE, TRUE),
               CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexC(TRUE, TRUE, yes, yes, commit, commit, notsent, FALSE))
CexS10 == CexS(CexP(yes, FALSE, commit, TRUE, TRUE),
               CexP(yes, TRUE, undecided, FALSE, TRUE),
               CexC(TRUE, TRUE, yes, yes, commit, commit, notsent, FALSE))
CexS11 == CexS(CexP(yes, FALSE, commit, TRUE, TRUE),
               CexP(yes, FALSE, undecided, TRUE, TRUE),
               CexC(TRUE, TRUE, yes, yes, commit, commit, notsent, FALSE))

CexTrace == <<CexS1, CexS2, CexS3, CexS4, CexS5, CexS6,
              CexS7, CexS8, CexS9, CexS10, CexS11>>

CexActionNames ==
  <<"request(p0)", "request(p1)", "sendVote(p0)", "sendVote(p1)",
    "coordDecide", "coordBroadcast(p0)", "coordDie",
    "receiveDecision(p0)", "participantDie(p0)", "participantDie(p1)">>

\* TLC-style counterexample: set of visited states and set of action edges,
\* closing with a stuttering lasso on the final state.
CounterExampleWitness ==
  [state  |-> { <<k, CexTrace[k]>> : k \in 1..Len(CexTrace) },
   action |-> { << <<k, CexTrace[k]>>,
                   [name |-> CexActionNames[k]],
                   <<k + 1, CexTrace[k + 1]>> >> : k \in 1..(Len(CexTrace) - 1) }
              \cup { << <<11, CexS11>>, [name |-> "Stuttering"], <<11, CexS11>> >> }]

PostCondition ==
  LET cex == CounterExampleWitness
      final == CexTrace[Len(CexTrace)]
  IN  /\ Cardinality(cex.state) = 11
      /\ Cardinality(cex.action) = 11
      /\ ~final.coordinator.alive
      /\ \A p \in CexParts : ~final.participant[p].alive
      /\ final.participant["p0"].decision = commit
      /\ final.participant["p1"].decision = undecided
      /\ ~(\A p \in CexParts : final.participant[p].decision = commit)

=============================================================================
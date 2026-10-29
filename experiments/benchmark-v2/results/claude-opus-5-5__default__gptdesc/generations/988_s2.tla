---------------------------- MODULE MC_ACP_NB ----------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS p0, p1

ASSUME p0 # p1

participants == {p0, p1}

yes       == "yes"
no        == "no"
undecided == "undecided"
commit    == "commit"
abort     == "abort"
waiting   == "waiting"
notsent   == "notsent"

VARIABLES participant, coordinator

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(* Underlying ACP_NB transition system                                   *)
---------------------------------------------------------------------------

TypeOK ==
  /\ participant \in [participants ->
        [ vote     : {yes, no},
          alive    : BOOLEAN,
          decision : {undecided, commit, abort},
          voteSent : BOOLEAN,
          forward  : [participants -> {notsent, commit, abort}] ]]
  /\ coordinator \in
        [ request   : [participants -> BOOLEAN],
          vote      : [participants -> {waiting, yes, no}],
          alive     : BOOLEAN,
          decision  : {undecided, commit, abort},
          broadcast : [participants -> {notsent, commit, abort}] ]

Init ==
  /\ participant \in [participants ->
        [ vote     : {yes, no},
          alive    : {TRUE},
          decision : {undecided},
          voteSent : {FALSE},
          forward  : {[k \in participants |-> notsent]} ]]
  /\ coordinator = [ request   |-> [i \in participants |-> FALSE],
                     vote      |-> [i \in participants |-> waiting],
                     alive     |-> TRUE,
                     decision  |-> undecided,
                     broadcast |-> [i \in participants |-> notsent] ]

\* Coordinator actions
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

\* Participant actions
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

\* Non-blocking extensions
parForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision \in {commit, abort}
  /\ participant[i].forward[j] = notsent
  /\ participant' = [participant EXCEPT ![i].forward[j] = participant[i].decision]
  /\ UNCHANGED coordinator

decideOnForward(i, j) ==
  /\ i # j
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[j].forward[i] \in {commit, abort}
  /\ participant' = [participant EXCEPT ![i].decision = participant[j].forward[i]]
  /\ UNCHANGED coordinator

abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ ~coordinator.alive
  /\ coordinator.broadcast[i] = notsent
  /\ \A j \in participants : participant[j].forward[i] = notsent
  /\ \A j \in participants :
        participant[j].alive => participant[j].decision \in {undecided, abort}
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

CoordProg ==
  \/ makeDecision
  \/ \E i \in participants :
        request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)

ParProg ==
  \E i \in participants :
     \/ sendVote(i) \/ abortOnVote(i) \/ abortOnTimeoutRequest(i)
     \/ decide(i) \/ abortOnTimeout(i)
     \/ \E j \in participants : parForward(i, j) \/ decideOnForward(i, j)

Failures ==
  \/ coordDie
  \/ \E i \in participants : parDie(i)

Next == CoordProg \/ ParProg \/ Failures

Spec == Init /\ [][Next]_vars /\ WF_vars(CoordProg) /\ WF_vars(ParProg)

---------------------------------------------------------------------------
(* Safety properties of atomic commitment                                *)
---------------------------------------------------------------------------

AC1 == \A i, j \in participants :
         ~ /\ participant[i].decision = commit
           /\ participant[j].decision = abort

AC2 == (\E i \in participants : participant[i].decision = commit)
         => \A j \in participants : participant[j].vote = yes

AC3_1 == (\E i \in participants : participant[i].vote = no)
         => \A j \in participants : participant[j].decision # commit

---------------------------------------------------------------------------
(* TLC wrapper definitions                                               *)
---------------------------------------------------------------------------

Perms == Permutations(participants)

AC4_alt ==
  [][ \A i \in participants :
        /\ participant[i].decision = commit => participant'[i].decision = commit
        /\ participant[i].decision = abort  => participant'[i].decision = abort
    ]_<<participant>>

AllMustCommit == <>(\A i \in participants : participant[i].decision = commit)

---------------------------------------------------------------------------
(* Concrete counterexample witness: coordinator failure, participant     *)
(* crashes, p1 never commits.                                            *)
---------------------------------------------------------------------------

NF == [k \in participants |-> notsent]

Pair(x, y) == (p0 :> x) @@ (p1 :> y)

PS(a, d, vs) == [ vote |-> yes, alive |-> a, decision |-> d,
                  voteSent |-> vs, forward |-> NF ]

CS(req, vt, a, d, bc) == [ request |-> req, vote |-> vt, alive |-> a,
                           decision |-> d, broadcast |-> bc ]

St(pp, cc) == [participant |-> pp, coordinator |-> cc]

Trace ==
  << St(Pair(PS(TRUE, undecided, FALSE), PS(TRUE, undecided, FALSE)),
        CS(Pair(FALSE, FALSE), Pair(waiting, waiting), TRUE, undecided, Pair(notsent, notsent))),
     St(Pair(PS(TRUE, undecided, FALSE), PS(TRUE, undecided, FALSE)),
        CS(Pair(TRUE, FALSE), Pair(waiting, waiting), TRUE, undecided, Pair(notsent, notsent))),
     St(Pair(PS(TRUE, undecided, FALSE), PS(TRUE, undecided, FALSE)),
        CS(Pair(TRUE, TRUE), Pair(waiting, waiting), TRUE, undecided, Pair(notsent, notsent))),
     St(Pair(PS(TRUE, undecided, TRUE), PS(TRUE, undecided, FALSE)),
        CS(Pair(TRUE, TRUE), Pair(waiting, waiting), TRUE, undecided, Pair(notsent, notsent))),
     St(Pair(PS(TRUE, undecided, TRUE), PS(TRUE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(waiting, waiting), TRUE, undecided, Pair(notsent, notsent))),
     St(Pair(PS(TRUE, undecided, TRUE), PS(TRUE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(yes, waiting), TRUE, undecided, Pair(notsent, notsent))),
     St(Pair(PS(TRUE, undecided, TRUE), PS(TRUE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(yes, yes), TRUE, undecided, Pair(notsent, notsent))),
     St(Pair(PS(TRUE, undecided, TRUE), PS(TRUE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(yes, yes), TRUE, commit, Pair(notsent, notsent))),
     St(Pair(PS(TRUE, undecided, TRUE), PS(TRUE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(yes, yes), TRUE, commit, Pair(commit, notsent))),
     St(Pair(PS(TRUE, undecided, TRUE), PS(TRUE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(yes, yes), FALSE, commit, Pair(commit, notsent))),
     St(Pair(PS(TRUE, undecided, TRUE), PS(FALSE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(yes, yes), FALSE, commit, Pair(commit, notsent))),
     St(Pair(PS(TRUE, commit, TRUE), PS(FALSE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(yes, yes), FALSE, commit, Pair(commit, notsent))),
     St(Pair(PS(FALSE, commit, TRUE), PS(FALSE, undecided, TRUE)),
        CS(Pair(TRUE, TRUE), Pair(yes, yes), FALSE, commit, Pair(commit, notsent)))
  >>

TraceActions ==
  << "Init", "request(p0)", "request(p1)", "sendVote(p0)", "sendVote(p1)",
     "getVote(p0)", "getVote(p1)", "makeDecision", "coordBroadcast(p0)",
     "coordDie", "parDie(p1)", "decide(p0)", "parDie(p0)" >>

PostCondition ==
  [ counterexample |->
      [ state  |-> { <<i, Trace[i]>> : i \in 1..Len(Trace) },
        action |-> { << <<i, Trace[i]>>,
                        [name |-> TraceActions[i + 1]],
                        <<i + 1, Trace[i + 1]>> >> : i \in 1..(Len(Trace) - 1) }
                   \cup
                   { << <<Len(Trace), Trace[Len(Trace)]>>,
                        [name |-> "Stuttering"],
                        <<Len(Trace), Trace[Len(Trace)]>> >> } ],
    visited     |-> { Trace[i] : i \in 1..Len(Trace) },
    trace       |-> Trace,
    loopsTo     |-> Len(Trace),
    violated    |-> "AllMustCommit",
    participants |-> <<p0, p1>> ]

===========================================================================
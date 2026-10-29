---------------------------- MODULE MC_ACP_SB ----------------------------
(***************************************************************************)
(* Typed wrapper for the Atomic Commit Protocol with Single Broadcast      *)
(* (ACP_SB). A coordinator collects votes from participants, decides,     *)
(* and broadcasts the decision to each participant exactly once. If the   *)
(* coordinator fails part-way through its broadcast, some participants    *)
(* may stay blocked. Deadlock checking is therefore disabled.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Set(Str);
    participants,
    \* @type: Str;
    yes,
    \* @type: Str;
    no,
    \* @type: Str;
    undecided,
    \* @type: Str;
    commit,
    \* @type: Str;
    abort,
    \* @type: Str;
    waiting,
    \* @type: Str;
    notsent

VARIABLES
    \* @type: Str -> [vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool];
    participant,
    \* @type: [request: Str -> Bool, vote: Str -> Str, broadcast: Str -> Str, decision: Str, alive: Bool, faulty: Bool];
    coordinator

vars == <<participant, coordinator>>

\* Concrete participant set used by the model-checking configuration
participantsVal == {"p1", "p2", "p3"}

---------------------------------------------------------------------------
(* Type invariant *)

TypeInv ==
    /\ participant \in [participants ->
                          [vote     : {yes, no},
                           alive    : BOOLEAN,
                           decision : {undecided, commit, abort},
                           faulty   : BOOLEAN,
                           voteSent : BOOLEAN]]
    /\ coordinator \in [request   : [participants -> BOOLEAN],
                        vote      : [participants -> {waiting, yes, no}],
                        broadcast : [participants -> {commit, abort, notsent}],
                        decision  : {commit, abort, undecided},
                        alive     : BOOLEAN,
                        faulty    : BOOLEAN]

---------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ participant \in [participants ->
                          [vote     : {yes, no},
                           alive    : {TRUE},
                           decision : {undecided},
                           faulty   : {FALSE},
                           voteSent : {FALSE}]]
    /\ coordinator = [request   |-> [i \in participants |-> FALSE],
                      vote      |-> [i \in participants |-> waiting],
                      broadcast |-> [i \in participants |-> notsent],
                      decision  |-> undecided,
                      alive     |-> TRUE,
                      faulty    |-> FALSE]

---------------------------------------------------------------------------
(* Coordinator actions *)

\* The coordinator sends a vote request to participant i
request(i) ==
    /\ coordinator.alive
    /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
    /\ UNCHANGED participant

\* The coordinator receives the vote of participant i
getVote(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.request[i]
    /\ coordinator.vote[i] = waiting
    /\ participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
    /\ UNCHANGED participant

\* The coordinator detects that participant i has failed before voting
detectFault(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.request[i]
    /\ coordinator.vote[i] = waiting
    /\ ~participant[i].alive
    /\ ~participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
    /\ UNCHANGED participant

\* The coordinator makes its decision after all votes are known
makeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.vote[j] # waiting
    /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
          /\ coordinator' = [coordinator EXCEPT !.decision = commit]
       \/ /\ \E j \in participants : coordinator.vote[j] = no
          /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED participant

\* The coordinator sends its decision to participant i (single broadcast)
coordBroadcast(i) ==
    /\ coordinator.alive
    /\ coordinator.decision # undecided
    /\ coordinator.broadcast[i] = notsent
    /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
    /\ UNCHANGED participant

\* The coordinator fails
coordDie ==
    /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
    /\ UNCHANGED participant

---------------------------------------------------------------------------
(* Participant actions *)

\* Participant i sends its vote after receiving a request
sendVote(i) ==
    /\ participant[i].alive
    /\ ~participant[i].voteSent
    /\ coordinator.request[i]
    /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
    /\ UNCHANGED coordinator

\* Participant i that voted no can abort unilaterally
abortOnVote(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[i].voteSent
    /\ participant[i].vote = no
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

\* Participant i aborts if the coordinator died before requesting its vote
abortOnTimeoutRequest(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ ~coordinator.request[i]
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

\* Participant i adopts the decision broadcast by the coordinator
decide(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ coordinator.broadcast[i] # notsent
    /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
    /\ UNCHANGED coordinator

\* Participant i fails
parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relations *)

parProg(i) ==
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ abortOnTimeoutRequest(i)
    \/ decide(i)

parFault(i) == parDie(i)

coordProg ==
    \/ \E i \in participants :
          \/ request(i)
          \/ getVote(i)
          \/ detectFault(i)
          \/ coordBroadcast(i)
    \/ makeDecision

coordFault == coordDie

\* Progress plus faults
progN ==
    \/ \E i \in participants : parProg(i) \/ parFault(i)
    \/ coordProg
    \/ coordFault

Spec == Init /\ [][progN]_vars

---------------------------------------------------------------------------
(* Correctness properties *)

AllCommit == \A i \in participants : participant[i].decision = commit
AllAbort  == \A i \in participants : participant[i].decision = abort

\* All participants that decided reached the same decision
AC1 == \A i, j \in participants :
          (participant[i].decision # undecided /\ participant[j].decision # undecided)
             => participant[i].decision = participant[j].decision

\* If any participant decides commit, then all participants voted yes
AC2 == (\E i \in participants : participant[i].decision = commit)
          => (\A j \in participants : participant[j].vote = yes)

\* If any participant decides abort, then some participant voted no or there was a failure
AC3 == (\E i \in participants : participant[i].decision = abort)
          => \/ \E j \in participants : participant[j].vote = no
             \/ \E j \in participants : participant[j].faulty
             \/ coordinator.faulty

=============================================================================
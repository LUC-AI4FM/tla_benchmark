---------------------------- MODULE APAACP_SB ----------------------------
(***************************************************************************)
(* Apalache-typed version of the Atomic Commit Protocol with a Single     *)
(* Broadcast (ACP_SB).  A coordinator asks every participant for a vote,  *)
(* collects the votes, decides commit/abort and broadcasts the decision.  *)
(* Participants and the coordinator may crash.  The single (reliable)     *)
(* broadcast ensures that a decision delivered to one participant is      *)
(* forwarded to all others.                                               *)
(*                                                                         *)
(* Intended configuration:                                                 *)
(*   participants <- {"p1","p2","p3"}                                      *)
(*   yes <- "yes", no <- "no", undecided <- "undecided",                   *)
(*   commit <- "commit", abort <- "abort",                                 *)
(*   waiting <- "waiting", notsent <- "notsent"                            *)
(*   INIT Init   NEXT progN   INVARIANT TypeInv   CHECK_DEADLOCK FALSE     *)
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
    \* @type: Str -> { vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool };
    participant,
    \* @type: { request: Str -> Bool, vote: Str -> Str, broadcast: Str -> Str, decision: Str, alive: Bool, faulty: Bool };
    coordinator

vars == <<participant, coordinator>>

\* Concrete instantiation values (for use with Apalache ConstInit)
ConstInit ==
    /\ participants = {"p1", "p2", "p3"}
    /\ yes = "yes"
    /\ no = "no"
    /\ undecided = "undecided"
    /\ commit = "commit"
    /\ abort = "abort"
    /\ waiting = "waiting"
    /\ notsent = "notsent"

-----------------------------------------------------------------------------
(* Type invariant *)

TypeInv ==
    /\ participant \in [participants ->
                          [ vote     : {yes, no},
                            alive    : BOOLEAN,
                            decision : {undecided, commit, abort},
                            faulty   : BOOLEAN,
                            voteSent : BOOLEAN ]]
    /\ coordinator \in [ request   : [participants -> BOOLEAN],
                         vote      : [participants -> {waiting, yes, no}],
                         broadcast : [participants -> {commit, abort, notsent}],
                         decision  : {commit, abort, undecided},
                         alive     : BOOLEAN,
                         faulty    : BOOLEAN ]

-----------------------------------------------------------------------------
(* Initial state *)

InitParticipant ==
    participant \in [participants ->
                       [ vote     : {yes, no},
                         alive    : {TRUE},
                         decision : {undecided},
                         faulty   : {FALSE},
                         voteSent : {FALSE} ]]

InitCoordinator ==
    coordinator = [ request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    broadcast |-> [i \in participants |-> notsent],
                    decision  |-> undecided,
                    alive     |-> TRUE,
                    faulty    |-> FALSE ]

Init == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
(* Coordinator actions *)

\* Coordinator sends a vote request to participant i
request(i) ==
    /\ coordinator.alive
    /\ ~coordinator.request[i]
    /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
    /\ UNCHANGED participant

\* Coordinator receives the vote of participant i
getVote(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.request[j]
    /\ coordinator.vote[i] = waiting
    /\ participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
    /\ UNCHANGED participant

\* Coordinator detects that participant i crashed before voting: abort
detectFault(i) ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ coordinator.request[i]
    /\ coordinator.vote[i] = waiting
    /\ ~participant[i].alive
    /\ ~participant[i].voteSent
    /\ coordinator' = [coordinator EXCEPT !.decision = abort]
    /\ UNCHANGED participant

\* Coordinator decides once all votes are in
makeDecision ==
    /\ coordinator.alive
    /\ coordinator.decision = undecided
    /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
    /\ coordinator' = [coordinator EXCEPT !.decision =
                          IF \A j \in participants : coordinator.vote[j] = yes
                          THEN commit ELSE abort]
    /\ UNCHANGED participant

\* Coordinator broadcasts its decision to participant i
coordBroadcast(i) ==
    /\ coordinator.alive
    /\ coordinator.decision # undecided
    /\ coordinator.broadcast[i] = notsent
    /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
    /\ UNCHANGED participant

\* Coordinator crashes
coordDie ==
    /\ coordinator.alive
    /\ coordinator' = [coordinator EXCEPT !.alive = FALSE, !.faulty = TRUE]
    /\ UNCHANGED participant

-----------------------------------------------------------------------------
(* Participant actions *)

\* Participant i answers the vote request
sendVote(i) ==
    /\ participant[i].alive
    /\ coordinator.request[i]
    /\ ~participant[i].voteSent
    /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
    /\ UNCHANGED coordinator

\* A participant that voted "no" may abort unilaterally
abortOnVote(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[i].voteSent
    /\ participant[i].vote = no
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

\* Coordinator crashed before requesting i's vote: i may abort
abortOnTimeoutRequest(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ ~coordinator.alive
    /\ ~coordinator.request[i]
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

\* Participant i delivers the coordinator's broadcast decision
decide(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ coordinator.broadcast[i] \in {commit, abort}
    /\ participant' = [participant EXCEPT ![i].decision = coordinator.broadcast[i]]
    /\ UNCHANGED coordinator

\* Single (reliable) broadcast: a participant that delivered the
\* coordinator's decision forwards it before delivering, so any other
\* participant may deliver it.
decideOnForward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ coordinator.broadcast[j] \in {commit, abort}
    /\ participant[j].decision = coordinator.broadcast[j]
    /\ participant' = [participant EXCEPT ![i].decision = participant[j].decision]
    /\ UNCHANGED coordinator

\* Participant i crashes
parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE, ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

-----------------------------------------------------------------------------
(* Next-state relation *)

coordProg ==
    \/ \E i \in participants :
          request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
    \/ makeDecision

parProg ==
    \E i \in participants :
        \/ sendVote(i)
        \/ abortOnVote(i)
        \/ abortOnTimeoutRequest(i)
        \/ decide(i)
        \/ \E j \in participants : decideOnForward(i, j)

progN ==
    \/ coordProg
    \/ parProg
    \/ coordDie
    \/ \E i \in participants : parDie(i)

Next == progN

\* Fairness: non-crash steps are weakly fair
Fairness ==
    /\ WF_vars(coordProg)
    /\ WF_vars(parProg)

Spec == Init /\ [][progN]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

\* AC1: all participants that decide reach the same decision
AC1 ==
    \A i, j \in participants :
        \/ participant[i].decision = undecided
        \/ participant[j].decision = undecided
        \/ participant[i].decision = participant[j].decision

\* AC2: commit only if all participants voted yes
AC2 ==
    (\E i \in participants : participant[i].decision = commit)
        => (\A j \in participants : participant[j].vote = yes)

\* AC3: if any participant voted no, nobody commits
AC3 ==
    (\E i \in participants : participant[i].vote = no)
        => (\A j \in participants : participant[j].decision # commit)

\* AC4: decisions are irreversible
AC4 ==
    [][\A i \in participants :
          participant[i].decision # undecided
             => participant'[i].decision = participant[i].decision]_vars

\* AC5 (liveness): every participant that stays alive eventually decides
AC5 ==
    \A i \in participants :
        <>(participant[i].decision # undecided \/ ~participant[i].alive)

Inv == TypeInv /\ AC1 /\ AC2 /\ AC3

THEOREM Spec => []Inv
=============================================================================
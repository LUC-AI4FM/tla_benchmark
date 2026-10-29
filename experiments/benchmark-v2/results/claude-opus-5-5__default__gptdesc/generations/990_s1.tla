------------------------------- MODULE ACP_NB -------------------------------
(***************************************************************************)
(* Non-blocking atomic commitment protocol variant.  Reliable broadcast   *)
(* is used to obtain the non-blocking property: when a participant        *)
(* receives a decision (from the coordinator or forwarded by another      *)
(* participant), it first forwards that decision to all other             *)
(* participants and only then locally delivers (decides) it.              *)
(* The base atomic commitment part (coordinator, voting, failures) is     *)
(* included directly so that the module is self-contained.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    participants,   \* set of participant identifiers
    yes, no,        \* votes
    undecided, commit, abort,  \* decisions
    waiting,        \* coordinator waiting for a vote
    notsent         \* message not yet sent

ASSUME
    /\ participants # {}
    /\ Cardinality({yes, no, undecided, commit, abort, waiting, notsent}) = 7

VARIABLES coordinator, participant

vars == <<coordinator, participant>>

-----------------------------------------------------------------------------
(* Type invariant *)

Coord ==
    [ request   : [participants -> BOOLEAN],
      vote      : [participants -> {waiting, yes, no}],
      broadcast : [participants -> {commit, abort, notsent}],
      decision  : {undecided, commit, abort},
      alive     : BOOLEAN ]

Participant ==
    [ vote     : {yes, no},
      alive    : BOOLEAN,
      decision : {undecided, commit, abort},
      faulty   : BOOLEAN,
      voteSent : BOOLEAN,
      forward  : [participants -> {notsent, commit, abort}] ]

TypeInfo ==
    /\ coordinator \in Coord
    /\ participant \in [participants -> Participant]

-----------------------------------------------------------------------------
(* Initial state *)

InitCoordinator ==
    coordinator = [ request   |-> [i \in participants |-> FALSE],
                    vote      |-> [i \in participants |-> waiting],
                    broadcast |-> [i \in participants |-> notsent],
                    decision  |-> undecided,
                    alive     |-> TRUE ]

InitParticipants ==
    participant \in [participants ->
                        [ vote     : {yes, no},
                          alive    : {TRUE},
                          decision : {undecided},
                          faulty   : {FALSE},
                          voteSent : {FALSE},
                          forward  : {[j \in participants |-> notsent]} ]]

Init == InitCoordinator /\ InitParticipants

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
    /\ coordinator' =
         [coordinator EXCEPT !.decision =
             IF \A i \in participants : coordinator.vote[i] = yes
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
    /\ participant[i].forward[i] = notsent
    /\ participant[i].voteSent
    /\ participant[i].vote = no
    /\ participant' = [participant EXCEPT ![i].decision = abort]
    /\ UNCHANGED coordinator

(* i forwards its received (pre-decided) decision to participant j *)
forward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].forward[i] # notsent
    /\ participant[i].forward[j] = notsent
    /\ participant' =
         [participant EXCEPT ![i].forward[j] = participant[i].forward[i]]
    /\ UNCHANGED coordinator

(* pre-decide upon receiving a decision forwarded by participant j *)
preDecideOnForward(i, j) ==
    /\ i # j
    /\ participant[i].alive
    /\ participant[i].forward[i] = notsent
    /\ participant[j].forward[i] # notsent
    /\ participant' =
         [participant EXCEPT ![i].forward[i] = participant[j].forward[i]]
    /\ UNCHANGED coordinator

(* pre-decide upon receiving the coordinator's decision *)
preDecide(i) ==
    /\ participant[i].alive
    /\ participant[i].forward[i] = notsent
    /\ coordinator.broadcast[i] # notsent
    /\ participant' =
         [participant EXCEPT ![i].forward[i] = coordinator.broadcast[i]]
    /\ UNCHANGED coordinator

(* deliver the decision once it has been forwarded to everybody *)
decide(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[i].forward[i] # notsent
    /\ \A j \in participants : participant[i].forward[j] # notsent
    /\ participant' =
         [participant EXCEPT ![i].decision = participant[i].forward[i]]
    /\ UNCHANGED coordinator

(* simulated timeout: the coordinator has crashed without broadcasting *)
(* any decision and no participant has received or forwarded one.     *)
abortOnTimeout(i) ==
    /\ participant[i].alive
    /\ participant[i].decision = undecided
    /\ participant[i].forward[i] = notsent
    /\ ~coordinator.alive
    /\ \A j \in participants : coordinator.broadcast[j] = notsent
    /\ \A j, k \in participants : participant[j].forward[k] = notsent
    /\ participant' = [participant EXCEPT ![i].forward[i] = abort]
    /\ UNCHANGED coordinator

parProg(i) ==
    \/ sendVote(i)
    \/ abortOnVote(i)
    \/ preDecide(i)
    \/ \E j \in participants : preDecideOnForward(i, j)
    \/ \E j \in participants : forward(i, j)
    \/ decide(i)
    \/ abortOnTimeout(i)

parDie(i) ==
    /\ participant[i].alive
    /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                          ![i].faulty = TRUE]
    /\ UNCHANGED coordinator

coordProg ==
    \/ \E i \in participants :
          request(i) \/ getVote(i) \/ detectFault(i) \/ coordBroadcast(i)
    \/ makeDecision

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ coordProg
    \/ coordDie
    \/ \E i \in participants : parProg(i) \/ parDie(i)

Fairness ==
    /\ WF_vars(makeDecision)
    /\ \A i \in participants :
          /\ WF_vars(request(i))
          /\ WF_vars(getVote(i))
          /\ WF_vars(detectFault(i))
          /\ WF_vars(coordBroadcast(i))
          /\ WF_vars(sendVote(i))
          /\ WF_vars(abortOnVote(i))
          /\ WF_vars(preDecide(i))
          /\ WF_vars(\E j \in participants : preDecideOnForward(i, j))
          /\ WF_vars(decide(i))
          /\ WF_vars(abortOnTimeout(i))
          /\ \A j \in participants : WF_vars(forward(i, j))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* AC1: all participants that decide reach the same decision *)
AC1 ==
    \A i, j \in participants :
        ~ /\ participant[i].decision = commit
          /\ participant[j].decision = abort

(* AC2: commit only if all participants voted yes *)
AC2 ==
    (\E i \in participants : participant[i].decision = commit)
        => (\A j \in participants : participant[j].vote = yes)

(* AC3: if any participant voted no, nobody commits *)
AC3 ==
    (\E i \in participants : participant[i].vote = no)
        => (\A j \in participants : participant[j].decision # commit)

(* AC4: decisions are irrevocable *)
AC4 ==
    [][\A i \in participants :
          participant[i].decision # undecided
              => participant'[i].decision = participant[i].decision]_vars

(* Forwarded decisions agree with each other *)
ForwardAgreement ==
    \A i, j, k, l \in participants :
        ~ /\ participant[i].forward[j] = commit
          /\ participant[k].forward[l] = abort

-----------------------------------------------------------------------------
(* Liveness properties (some intentionally invalid) *)

(* Non-blocking: every correct participant eventually decides *)
AC5 ==
    \A i \in participants :
        <>(participant[i].decision # undecided \/ participant[i].faulty)

(* INVALID: every participant eventually commits or fails *)
AllCommit ==
    \A i \in participants :
        <>(participant[i].decision = commit \/ participant[i].faulty)

(* INVALID: every participant eventually aborts or fails *)
AllAbort ==
    \A i \in participants :
        <>(participant[i].decision = abort \/ participant[i].faulty)

(* INVALID: all yes votes lead to everybody committing *)
AllYesVotesLeadToCommit ==
    (\A i \in participants : participant[i].vote = yes)
        ~> (\A i \in participants : participant[i].decision = commit)

=============================================================================
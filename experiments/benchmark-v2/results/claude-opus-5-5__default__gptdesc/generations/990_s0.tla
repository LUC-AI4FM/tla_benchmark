---------------------------- MODULE ACP_NB ----------------------------
(***************************************************************************)
(* Non-blocking atomic commitment protocol.  Reliable broadcast provides   *)
(* the non-blocking property: when a participant receives a decision, it   *)
(* first forwards that decision to every other participant, and only then *)
(* delivers (decides) it locally.                                          *)
(*                                                                         *)
(* This module is self-contained.  It includes the base atomic commitment  *)
(* part (coordinator, votes, failures) and extends it with the participant *)
(* forwarding state.                                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS participants          \* set of participant identifiers

ASSUME participants # {}

VARIABLES participant,          \* participant states
          coordinator           \* coordinator state

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(*************************** Type invariant *******************************)

ForwardState == {"notsent", "commit", "abort"}

TypeOK ==
  /\ participant \in [participants ->
        [ vote     : {"yes", "no"},
          alive    : BOOLEAN,
          decision : {"undecided", "commit", "abort"},
          faulty   : BOOLEAN,
          voteSent : BOOLEAN,
          forward  : [participants -> ForwardState] ]]
  /\ coordinator \in
        [ request   : [participants -> BOOLEAN],
          vote      : [participants -> {"waiting", "yes", "no"}],
          broadcast : [participants -> {"notsent", "commit", "abort"}],
          decision  : {"undecided", "commit", "abort"},
          alive     : BOOLEAN ]

---------------------------------------------------------------------------
(****************************** Initial state *****************************)

Init ==
  /\ participant \in [participants ->
        [ vote     : {"yes", "no"},
          alive    : {TRUE},
          decision : {"undecided"},
          faulty   : {FALSE},
          voteSent : {FALSE},
          forward  : {[j \in participants |-> "notsent"]} ]]
  /\ coordinator =
        [ request   |-> [i \in participants |-> FALSE],
          vote      |-> [i \in participants |-> "waiting"],
          broadcast |-> [i \in participants |-> "notsent"],
          decision  |-> "undecided",
          alive     |-> TRUE ]

---------------------------------------------------------------------------
(*************************** Coordinator actions **************************)

\* Coordinator sends a vote request to participant i
request(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* Coordinator reaches a decision
decide ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ \/ /\ \A i \in participants : coordinator.vote[i] = "yes"
        /\ coordinator' = [coordinator EXCEPT !.decision = "commit"]
     \/ /\ \E i \in participants : coordinator.vote[i] = "no"
        /\ coordinator' = [coordinator EXCEPT !.decision = "abort"]
  /\ UNCHANGED participant

\* Coordinator broadcasts its decision to participant i
broadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # "undecided"
  /\ coordinator.broadcast[i] = "notsent"
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = coordinator.decision]
  /\ UNCHANGED participant

\* Coordinator crashes
coordFail ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

coordProg ==
  \/ \E i \in participants : request(i) \/ broadcast(i)
  \/ decide

---------------------------------------------------------------------------
(********************* Base participant actions ***************************)

\* Participant i answers the vote request
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]

\* A participant that voted "no" may abort unilaterally
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].voteSent
  /\ participant[i].vote = "no"
  /\ participant[i].decision = "undecided"
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

\* Participant i crashes
parFail(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                        ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(******************* Non-blocking participant actions *********************)

\* Participant i forwards its pre-decision to participant j
parProgNB(i, j) ==
  /\ participant[i].alive
  /\ i # j
  /\ participant[i].forward[i] # "notsent"
  /\ participant[i].forward[j] = "notsent"
  /\ participant' = [participant EXCEPT
                       ![i].forward[j] = participant[i].forward[i]]
  /\ UNCHANGED coordinator

\* Participant i pre-decides on a decision forwarded by participant j
preDecideOnForward(i, j) ==
  /\ participant[i].alive
  /\ i # j
  /\ participant[i].forward[i] = "notsent"
  /\ participant[j].forward[i] # "notsent"
  /\ participant' = [participant EXCEPT
                       ![i].forward[i] = participant[j].forward[i]]
  /\ UNCHANGED coordinator

\* Participant i pre-decides on the coordinator's broadcast
preDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].forward[i] = "notsent"
  /\ coordinator.broadcast[i] # "notsent"
  /\ participant' = [participant EXCEPT
                       ![i].forward[i] = coordinator.broadcast[i]]
  /\ UNCHANGED coordinator

\* Participant i decides once it has forwarded its decision to everyone
decideNB(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ participant[i].forward[i] # "notsent"
  /\ \A j \in participants : participant[i].forward[j] # "notsent"
  /\ participant' = [participant EXCEPT
                       ![i].decision = participant[i].forward[i]]
  /\ UNCHANGED coordinator

\* Participant i aborts on (simulated) timeout: the coordinator has crashed
\* and no live participant has pre-decided or forwarded anything to i.
abortOnTimeout(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ participant[i].forward[i] = "notsent"
  /\ ~coordinator.alive
  /\ coordinator.broadcast[i] = "notsent"
  /\ \A j \in participants :
        /\ participant[j].forward[i] = "notsent"
        /\ participant[j].alive => participant[j].forward[j] = "notsent"
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ preDecide(i)
  \/ decideNB(i)
  \/ abortOnTimeout(i)
  \/ \E j \in participants : parProgNB(i, j) \/ preDecideOnForward(i, j)

---------------------------------------------------------------------------
(**************************** Specification *******************************)

Next ==
  \/ coordProg
  \/ coordFail
  \/ \E i \in participants : parProg(i) \/ parFail(i)

Fairness ==
  /\ WF_vars(coordProg)
  /\ \A i \in participants :
        /\ WF_vars(sendVote(i))
        /\ WF_vars(abortOnVote(i))
        /\ WF_vars(preDecide(i))
        /\ WF_vars(decideNB(i))
        /\ WF_vars(abortOnTimeout(i))
        /\ \A j \in participants :
              /\ WF_vars(parProgNB(i, j))
              /\ WF_vars(preDecideOnForward(i, j))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(*************************** Safety properties ****************************)

\* AC1: all participants that decide reach the same decision
AC1 ==
  \A i, j \in participants :
     \/ participant[i].decision # "commit"
     \/ participant[j].decision # "abort"

\* AC2: commit only if all participants voted yes
AC2 ==
  (\E i \in participants : participant[i].decision = "commit")
     => \A j \in participants : participant[j].vote = "yes"

\* AC3_1: if any participant voted no, nobody commits
AC3_1 ==
  (\E i \in participants : participant[i].vote = "no")
     => \A j \in participants : participant[j].decision # "commit"

\* AC4: decisions are irreversible
AC4 ==
  [][\A i \in participants :
       participant[i].decision # "undecided"
          => participant'[i].decision = participant[i].decision]_vars

\* Forwarded values are consistent with what is pre-decided
ForwardConsistent ==
  \A i, j \in participants :
     participant[i].forward[j] # "notsent"
        => participant[i].forward[j] = participant[i].forward[i]

---------------------------------------------------------------------------
(************************** Liveness properties ***************************)

\* AC3_2: if all vote yes and no failures occur, everyone eventually commits
AC3_2 ==
  <>[]( (/\ \A i \in participants : participant[i].vote = "yes"
         /\ \A i \in participants : ~participant[i].faulty
         /\ coordinator.alive)
        => \A i \in participants : participant[i].decision = "commit" )

\* AC5 (non-blocking termination): every live participant eventually decides
AC5 ==
  <>(\A i \in participants :
        participant[i].alive => participant[i].decision # "undecided")

---------------------------------------------------------------------------
(*********************** Invalid properties (expected to fail) ************)

AllCommit ==
  \A i \in participants : <>(participant[i].decision = "commit")

AllAbort ==
  \A i \in participants : <>(participant[i].decision = "abort")

AllVoteYes_LeadsTo_AllCommit ==
  (\A i \in participants : participant[i].vote = "yes")
     ~> (\A i \in participants : participant[i].decision = "commit")

=============================================================================
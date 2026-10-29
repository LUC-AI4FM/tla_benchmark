------------------------------- MODULE ACP_NB -------------------------------
(***************************************************************************)
(* Atomic commitment protocol with one coordinator and a set of            *)
(* participants, using a simple broadcast mechanism.                       *)
(*                                                                         *)
(* - Synchronous communication has been replaced by implicit asynchronous  *)
(*   communication: a process reads the relevant state of its peer.        *)
(* - Failures are detected "magically" by inspecting the alive / faulty    *)
(*   flags of other processes, instead of via timeouts.                    *)
(* - Broadcast is modeled as a sequence of individual sends, one per       *)
(*   participant. The coordinator may fail in the middle of a broadcast.   *)
(*   Participants that voted yes and did not receive the decision then     *)
(*   wait forever. The protocol is therefore non-terminating, and the      *)
(*   usual termination property AC5 does NOT hold.                         *)
(***************************************************************************)

CONSTANTS
  participants,          \* set of participants
  yes, no,               \* votes
  undecided, commit, abort,  \* decisions
  waiting                \* coordinator has not yet received a vote

VARIABLES
  participant,           \* participant states
  coordinator            \* coordinator state

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Type invariants                                                         *)
(***************************************************************************)

TypeInvParticipant ==
  participant \in [participants ->
                     [ vote     : {yes, no},
                       alive    : BOOLEAN,
                       decision : {undecided, commit, abort},
                       faulty   : BOOLEAN,
                       voteSent : BOOLEAN ]]

TypeInvCoordinator ==
  coordinator \in [ request   : [participants -> BOOLEAN],
                    vote      : [participants -> {waiting, yes, no}],
                    alive     : BOOLEAN,
                    decision  : {undecided, commit, abort},
                    broadcast : [participants -> BOOLEAN] ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

---------------------------------------------------------------------------
(***************************************************************************)
(* Initial states                                                          *)
(***************************************************************************)

InitParticipant ==
  participant \in [participants ->
                     [ vote     : {yes, no},
                       alive    : {TRUE},
                       decision : {undecided},
                       faulty   : {FALSE},
                       voteSent : {FALSE} ]]

InitCoordinator ==
  coordinator \in [ request   : [participants -> {FALSE}],
                    vote      : [participants -> {waiting}],
                    alive     : {TRUE},
                    decision  : {undecided},
                    broadcast : [participants -> {FALSE}] ]

Init == InitParticipant /\ InitCoordinator

---------------------------------------------------------------------------
(***************************************************************************)
(* Participant actions                                                     *)
(***************************************************************************)

\* Participant i sends its vote after receiving the coordinator's request.
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~ participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* A participant that voted no may unilaterally abort.
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* The coordinator died before requesting i's vote: i may abort.
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~ coordinator.alive
  /\ ~ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* Participant i receives the coordinator's broadcast decision.
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i]
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
  /\ UNCHANGED coordinator

\* Participant i fails.
parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ decide(i)

parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                        ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)

\* The coordinator requests the vote of participant i.
request(i) ==
  /\ coordinator.alive
  /\ ~ coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* The coordinator receives the vote of participant i.
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* The coordinator (magically) detects the failure of participant i
\* whose vote it is still waiting for, and decides abort.
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[i] = waiting
  /\ participant[i].faulty
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Once all votes are in, the coordinator decides.
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = yes
        /\ coordinator' = [coordinator EXCEPT !.decision = commit]
     \/ /\ \E j \in participants : coordinator.vote[j] = no
        /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED participant

\* Simple broadcast: send the decision to participant i
\* (one individual send of the broadcast sequence).
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ ~ coordinator.broadcast[i]
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
  /\ UNCHANGED participant

\* The coordinator fails (possibly in the middle of a broadcast).
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

coordProgA(i) ==
  \/ request(i)
  \/ getVote(i)
  \/ detectFault(i)
  \/ coordBroadcast(i)

coordProgB == makeDecision

---------------------------------------------------------------------------
(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)

Next ==
  \/ \E i \in participants : parProg(i) \/ parDie(i)
  \/ \E i \in participants : coordProgA(i)
  \/ coordProgB
  \/ coordDie

\* Weak fairness on all progress actions, but not on failures.
Fairness ==
  /\ \A i \in participants : WF_vars(parProg(i))
  /\ \A i \in participants : WF_vars(coordProgA(i))
  /\ WF_vars(coordProgB)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* AC1: All participants that decide reach the same decision.
AC1 ==
  [] \A i, j \in participants :
       ~ (participant[i].decision = commit /\ participant[j].decision = abort)

\* AC2: If any participant decides commit, then all participants voted yes.
AC2 ==
  [] ( (\E i \in participants : participant[i].decision = commit)
       => (\A j \in participants : participant[j].vote = yes) )

\* AC3_1: If any participant decides abort, then some participant voted no,
\* or some process failed.
AC3_1 ==
  [] ( (\E i \in participants : participant[i].decision = abort)
       => \/ \E j \in participants : participant[j].vote = no
          \/ \E j \in participants : participant[j].faulty
          \/ ~ coordinator.alive )

\* AC4: Decisions are irrevocable.
AC4 ==
  [][ \A i \in participants :
        participant[i].decision # undecided
          => participant'[i].decision = participant[i].decision ]_vars

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* AC3_2: If all participants vote yes and no failures occur,
\* then all participants eventually decide commit.
AC3_2 ==
  <> [] ( ( /\ \A i \in participants : participant[i].alive
            /\ \A i \in participants : participant[i].vote = yes
            /\ coordinator.alive )
          => \A i \in participants : participant[i].decision = commit )

\* If the coordinator stays alive, every live participant eventually decides.
CoordAliveTermination ==
  <> [] ( coordinator.alive
          => \A i \in participants :
               participant[i].alive => participant[i].decision # undecided )

(***************************************************************************)
(* Stronger auxiliary properties                                           *)
(***************************************************************************)

\* A participant's decision agrees with the coordinator's decision,
\* unless the participant aborted on its own.
AC1_Coord ==
  [] \A i \in participants :
       /\ participant[i].decision = commit => coordinator.decision = commit
       /\ (participant[i].decision = abort /\ coordinator.decision # undecided)
            => coordinator.decision = abort

\* If the coordinator decides commit, all participants voted yes.
AC2_Coord ==
  [] ( coordinator.decision = commit
       => \A j \in participants : participant[j].vote = yes )

\* The coordinator's decision is irrevocable.
AC4_Coord ==
  [][ coordinator.decision # undecided
        => coordinator'.decision = coordinator.decision ]_vars

\* The coordinator only records votes actually sent.
VoteConsistency ==
  [] \A i \in participants :
       coordinator.vote[i] # waiting
         => /\ participant[i].voteSent
            /\ coordinator.vote[i] = participant[i].vote

\* A broadcast to i only happens after a decision.
BroadcastConsistency ==
  [] \A i \in participants :
       coordinator.broadcast[i] => coordinator.decision # undecided

(***************************************************************************)
(* Invalid properties (expected to be violated)                            *)
(***************************************************************************)

\* AC5: Every live participant eventually decides. Does NOT hold, since the
\* coordinator may fail in the middle of the broadcast, leaving
\* participants that voted yes blocked forever.
AC5 ==
  <> \A i \in participants :
       participant[i].alive => participant[i].decision # undecided

\* All participants eventually decide commit whenever all voted yes,
\* regardless of failures. Does NOT hold.
InvalidAC3 ==
  <> [] ( (\A i \in participants : participant[i].vote = yes)
          => \A i \in participants : participant[i].decision = commit )

\* Some participant always decides. Does NOT hold.
InvalidSomeDecides ==
  <> \E i \in participants : participant[i].decision # undecided

---------------------------------------------------------------------------

THEOREM Spec => [] TypeInv
THEOREM Spec => AC1 /\ AC2 /\ AC3_1 /\ AC4
THEOREM Spec => AC3_2
THEOREM Spec => AC1_Coord /\ AC2_Coord /\ AC4_Coord
                /\ VoteConsistency /\ BroadcastConsistency

=============================================================================
------------------------------- MODULE ACP_SB -------------------------------
(***************************************************************************)
(* Atomic Commitment Protocol with one coordinator and a set of            *)
(* participants, using a simple broadcast primitive in an asynchronous     *)
(* setting.                                                                *)
(*                                                                         *)
(* - Synchronous communication has been replaced by implicit asynchronous *)
(*   communication: a process reads the relevant state of its peer.        *)
(* - Failures are detected "magically" by reading the alive flag of the    *)
(*   peer process, rather than by using timeouts.                          *)
(* - Broadcast is modeled as a sequence of individual sends, and a failure *)
(*   of the coordinator can interrupt it. The protocol is therefore        *)
(*   non-terminating (blocking), and the termination property AC5 does     *)
(*   not hold.                                                             *)
(***************************************************************************)

CONSTANTS
  participants,   \* set of participants
  yes, no,        \* vote values
  undecided, commit, abort,  \* decision values
  waiting         \* coordinator has not yet received a participant's vote

ASSUME
  /\ yes # no
  /\ undecided # commit /\ undecided # abort /\ commit # abort
  /\ waiting \notin {yes, no}

VARIABLES
  participant,    \* participant states
  coordinator     \* coordinator state

vars == <<participant, coordinator>>

---------------------------------------------------------------------------
(* Type information *)

TypeInfo ==
  /\ participant \in [participants -> [vote     : {yes, no},
                                       alive    : BOOLEAN,
                                       decision : {undecided, commit, abort},
                                       faulty   : BOOLEAN,
                                       voteSent : BOOLEAN]]
  /\ coordinator \in [request   : [participants -> BOOLEAN],
                      vote      : [participants -> {waiting, yes, no}],
                      alive     : BOOLEAN,
                      decision  : {undecided, commit, abort},
                      broadcast : [participants -> BOOLEAN]]

---------------------------------------------------------------------------
(* Initial states *)

InitParticipant ==
  participant \in [participants -> [vote     : {yes, no},
                                    alive    : {TRUE},
                                    decision : {undecided},
                                    faulty   : {FALSE},
                                    voteSent : {FALSE}]]

InitCoordinator ==
  coordinator \in [request   : [participants -> {FALSE}],
                   vote      : [participants -> {waiting}],
                   alive     : {TRUE},
                   decision  : {undecided},
                   broadcast : [participants -> {FALSE}]]

Init == InitParticipant /\ InitCoordinator

---------------------------------------------------------------------------
(* Coordinator actions *)

\* send a vote request to participant i
request(i) ==
  /\ coordinator.alive
  /\ ~ coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* receive the vote of participant i
getVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* detect the failure of participant i before it sent its vote
detectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.request[j]
  /\ coordinator.vote[i] = waiting
  /\ ~ participant[i].alive
  /\ ~ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = no]
  /\ UNCHANGED participant

\* make a decision once all votes are known
makeDecision ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A j \in participants : coordinator.vote[j] \in {yes, no}
  /\ coordinator' = [coordinator EXCEPT !.decision =
                        IF \A j \in participants : coordinator.vote[j] = yes
                        THEN commit ELSE abort]
  /\ UNCHANGED participant

\* broadcast the decision to participant i (one send of the broadcast)
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ ~ coordinator.broadcast[i]
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = TRUE]
  /\ UNCHANGED participant

\* the coordinator fails
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

---------------------------------------------------------------------------
(* Participant actions *)

\* reply to the coordinator's vote request
sendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~ participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* a participant voting no may abort unilaterally
abortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ participant[i].voteSent
  /\ participant[i].vote = no
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* coordinator failed before sending the vote request: abort
abortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ ~ coordinator.alive
  /\ ~ coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = abort]
  /\ UNCHANGED coordinator

\* receive the coordinator's decision
decide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = undecided
  /\ coordinator.broadcast[i]
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
  /\ UNCHANGED coordinator

\* participant i fails
parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE,
                                        ![i].faulty = TRUE]
  /\ UNCHANGED coordinator

---------------------------------------------------------------------------
(* Next-state relation and specification *)

parProg(i) ==
  \/ sendVote(i)
  \/ abortOnVote(i)
  \/ abortOnTimeoutRequest(i)
  \/ decide(i)

parProgN == \E i \in participants : parProg(i)

coordProgA(i) ==
  \/ request(i)
  \/ getVote(i)
  \/ detectFault(i)
  \/ coordBroadcast(i)

coordProgN ==
  \/ \E i \in participants : coordProgA(i)
  \/ makeDecision

progNotDeath == parProgN \/ coordProgN

Death == coordDie \/ \E i \in participants : parDie(i)

Next == progNotDeath \/ Death

Fairness ==
  /\ \A i \in participants : WF_vars(parProg(i))
  /\ \A i \in participants : WF_vars(coordProgA(i))
  /\ WF_vars(makeDecision)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

\* All participants that decide reach the same decision
AC1 == [] \A i, j \in participants :
            ~ (participant[i].decision = commit /\ participant[j].decision = abort)

\* If any participant decides commit, then all participants voted yes
AC2 == [] ( (\E i \in participants : participant[i].decision = commit)
            => (\A j \in participants : participant[j].vote = yes) )

\* If any participant votes no, then no participant decides commit
AC3_1 == [] ( (\E i \in participants : participant[i].vote = no)
              => (\A j \in participants : participant[j].decision # commit) )

\* Decisions are irreversible
AC4 == [][ \A i \in participants :
             participant[i].decision # undecided
             => participant'[i].decision = participant[i].decision ]_vars

---------------------------------------------------------------------------
(* Liveness property *)

\* If all participants vote yes and there are no failures, then
\* eventually all participants decide commit
AC3_2 == <> \/ \A i \in participants : participant[i].decision = commit
            \/ \E i \in participants : participant[i].vote = no
            \/ \E i \in participants : participant[i].faulty
            \/ ~ coordinator.alive

---------------------------------------------------------------------------
(* Stronger auxiliary properties used in proving the above *)

\* participant decisions are consistent with the coordinator's decision
AC1_strong == [] \A i \in participants :
                  /\ participant[i].decision = commit => coordinator.decision = commit
                  /\ participant[i].decision = abort  => coordinator.decision # commit

\* the coordinator commits only if all participants voted yes
AC2_strong == [] ( coordinator.decision = commit
                   => \A j \in participants : participant[j].vote = yes )

\* the coordinator commits only if it received yes from everyone
AC2_coord == [] ( coordinator.decision = commit
                  => \A j \in participants : coordinator.vote[j] = yes )

\* votes recorded by the coordinator are genuine (or due to detected failure)
VoteConsistency == [] \A i \in participants :
                      coordinator.vote[i] = yes => participant[i].vote = yes

---------------------------------------------------------------------------
(* Invalid properties: these do NOT hold for this protocol *)

\* Termination: all non-faulty participants eventually decide
AC5 == <> \A i \in participants :
            participant[i].alive => participant[i].decision # undecided

\* Commit regardless of failures (fails since processes may die)
AC3_2_noFaults == <> \/ \A i \in participants : participant[i].decision = commit
                     \/ \E i \in participants : participant[i].vote = no

=============================================================================
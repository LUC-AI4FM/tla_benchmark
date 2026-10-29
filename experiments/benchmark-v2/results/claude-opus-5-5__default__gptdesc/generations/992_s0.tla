-------------------------------- MODULE ACP_SB --------------------------------
(*****************************************************************************)
(* Atomic commitment protocol with one coordinator and a set of            *)
(* participants, using a simple broadcast mechanism (ACP-SB).               *)
(*                                                                           *)
(* Modelling notes:                                                          *)
(*  - Synchronous communication from the original presentation is replaced  *)
(*    by implicit asynchronous communication: processes read the relevant   *)
(*    parts of each other's state directly.                                  *)
(*  - Failures are detected "magically", by inspecting the alive flags of   *)
(*    other processes, rather than through timeouts.                         *)
(*  - Broadcast is a sequence of individual sends, one per participant.     *)
(*    The coordinator can fail partway through that sequence. Participants  *)
(*    that voted yes and never got the decision then block forever. The     *)
(*    protocol is therefore non-terminating, and the usual termination      *)
(*    property AC5 does not hold.                                            *)
(*****************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT participants          \* the set of participants

VARIABLES
  participant,                 \* participant states
  coordinator                  \* coordinator state

vars == << participant, coordinator >>

Votes     == {"yes", "no"}
Decisions == {"undecided", "commit", "abort"}

-----------------------------------------------------------------------------
(* Type invariants *)

TypeInvParticipant ==
  participant \in [ participants ->
                      [ vote     : Votes,
                        alive    : BOOLEAN,
                        decision : Decisions,
                        voteSent : BOOLEAN ] ]

TypeInvCoordinator ==
  coordinator \in [ request   : [participants -> BOOLEAN],
                    vote      : [participants -> {"waiting", "yes", "no"}],
                    broadcast : [participants -> {"notsent", "sent"}],
                    decision  : Decisions,
                    alive     : BOOLEAN ]

TypeInv == TypeInvParticipant /\ TypeInvCoordinator

-----------------------------------------------------------------------------
(* Initial states: every participant may vote either way, and all processes *)
(* are alive and undecided.                                                 *)

InitParticipant ==
  participant \in [ participants ->
                      [ vote     : Votes,
                        alive    : {TRUE},
                        decision : {"undecided"},
                        voteSent : {FALSE} ] ]

InitCoordinator ==
  coordinator = [ request   |-> [i \in participants |-> FALSE],
                  vote      |-> [i \in participants |-> "waiting"],
                  broadcast |-> [i \in participants |-> "notsent"],
                  decision  |-> "undecided",
                  alive     |-> TRUE ]

Init == InitParticipant /\ InitCoordinator

-----------------------------------------------------------------------------
(* Participant actions *)

\* Participant i has received the vote request and sends its vote.
parSendVote(i) ==
  /\ participant[i].alive
  /\ coordinator.request[i]
  /\ ~participant[i].voteSent
  /\ participant' = [participant EXCEPT ![i].voteSent = TRUE]
  /\ UNCHANGED coordinator

\* A participant that voted no may unilaterally decide abort.
parAbortOnVote(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ participant[i].voteSent
  /\ participant[i].vote = "no"
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

\* Suppose the coordinator fails before requesting participant i's vote.
\* Participant i detects the failure (magically) and aborts.
parAbortOnTimeoutRequest(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ ~coordinator.alive
  /\ ~coordinator.request[i]
  /\ participant' = [participant EXCEPT ![i].decision = "abort"]
  /\ UNCHANGED coordinator

\* Participant i receives the broadcast decision.
parDecide(i) ==
  /\ participant[i].alive
  /\ participant[i].decision = "undecided"
  /\ coordinator.broadcast[i] = "sent"
  /\ participant' = [participant EXCEPT ![i].decision = coordinator.decision]
  /\ UNCHANGED coordinator

\* Participant i fails (crash, no recovery).
parDie(i) ==
  /\ participant[i].alive
  /\ participant' = [participant EXCEPT ![i].alive = FALSE]
  /\ UNCHANGED coordinator

parProg(i) ==
  \/ parSendVote(i)
  \/ parAbortOnVote(i)
  \/ parAbortOnTimeoutRequest(i)
  \/ parDecide(i)

-----------------------------------------------------------------------------
(* Coordinator actions *)

\* The coordinator sends a vote request to participant i.
coordSendReq(i) ==
  /\ coordinator.alive
  /\ ~coordinator.request[i]
  /\ coordinator' = [coordinator EXCEPT !.request[i] = TRUE]
  /\ UNCHANGED participant

\* The coordinator receives participant i's vote.
coordGetVote(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ coordinator.vote[i] = "waiting"
  /\ participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.vote[i] = participant[i].vote]
  /\ UNCHANGED participant

\* The coordinator (magically) detects that participant i died before
\* sending its vote, and decides abort.
coordDetectFault(i) ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ coordinator.vote[i] = "waiting"
  /\ ~participant[i].alive
  /\ ~participant[i].voteSent
  /\ coordinator' = [coordinator EXCEPT !.decision = "abort"]
  /\ UNCHANGED participant

\* All votes have been received, so the coordinator decides.
coordDecide ==
  /\ coordinator.alive
  /\ coordinator.decision = "undecided"
  /\ \A j \in participants : coordinator.vote[j] # "waiting"
  /\ \/ /\ \A j \in participants : coordinator.vote[j] = "yes"
        /\ coordinator' = [coordinator EXCEPT !.decision = "commit"]
     \/ /\ \E j \in participants : coordinator.vote[j] = "no"
        /\ coordinator' = [coordinator EXCEPT !.decision = "abort"]
  /\ UNCHANGED participant

\* One step of the simple broadcast: send the decision to participant i.
coordBroadcast(i) ==
  /\ coordinator.alive
  /\ coordinator.decision # "undecided"
  /\ coordinator.broadcast[i] = "notsent"
  /\ coordinator' = [coordinator EXCEPT !.broadcast[i] = "sent"]
  /\ UNCHANGED participant

\* The coordinator fails (crash, no recovery).
coordDie ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED participant

coordProgA(i) ==
  \/ coordSendReq(i)
  \/ coordGetVote(i)
  \/ coordDetectFault(i)
  \/ coordBroadcast(i)

coordProgB == coordDecide

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
  \/ \E i \in participants : parProg(i) \/ parDie(i)
  \/ \E i \in participants : coordProgA(i)
  \/ coordProgB
  \/ coordDie

\* Weak fairness on all progress actions; none on the death actions.
Fairness ==
  /\ \A i \in participants : WF_vars(parProg(i))
  /\ \A i \in participants : WF_vars(coordProgA(i))
  /\ WF_vars(coordProgB)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* AC1: all participants that decide reach the same decision.
AC1 ==
  \A i, j \in participants :
    \/ participant[i].decision = "undecided"
    \/ participant[j].decision = "undecided"
    \/ participant[i].decision = participant[j].decision

\* AC2: if any participant decides commit, then all participants voted yes.
AC2 ==
  (\E i \in participants : participant[i].decision = "commit")
    => (\A j \in participants : participant[j].vote = "yes")

\* AC3_1: if any participant decides abort, then some participant voted no
\* or some process failed.
AC3_1 ==
  (\E i \in participants : participant[i].decision = "abort")
    => \/ \E j \in participants : participant[j].vote = "no"
       \/ \E j \in participants : ~participant[j].alive
       \/ ~coordinator.alive

\* AC4: decisions are irreversible.
AC4 ==
  [][ \A i \in participants :
        participant[i].decision # "undecided"
          => participant'[i].decision = participant[i].decision ]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* AC3_2: if all participants vote yes and no process ever fails,
\* then eventually all participants decide commit.
AC3_2 ==
  ( /\ \A i \in participants : participant[i].vote = "yes"
    /\ [](coordinator.alive /\ \A i \in participants : participant[i].alive) )
  => <>(\A i \in participants : participant[i].decision = "commit")

-----------------------------------------------------------------------------
(* Stronger auxiliary properties *)

\* A participant only commits if the coordinator has decided commit.
CommitImpliesCoordCommit ==
  \A i \in participants :
    participant[i].decision = "commit" => coordinator.decision = "commit"

\* A participant that has aborted is never contradicted by a commit
\* decision of the coordinator.
AbortImpliesNotCoordCommit ==
  \A i \in participants :
    participant[i].decision = "abort" => coordinator.decision # "commit"

\* A decided participant agrees with the coordinator's decision, unless it
\* aborted on its own.
DecisionConsistent ==
  \A i \in participants :
    (participant[i].decision # "undecided"
       /\ coordinator.decision # "undecided")
      => participant[i].decision = coordinator.decision

\* The coordinator's decision is irreversible.
CoordDecisionStable ==
  [][ coordinator.decision # "undecided"
        => coordinator'.decision = coordinator.decision ]_vars

\* Once the decision is sent to a live participant, it eventually decides.
BroadcastLeadsToDecision ==
  \A i \in participants :
    (coordinator.broadcast[i] = "sent" /\ participant[i].alive)
      ~> (participant[i].decision # "undecided" \/ ~participant[i].alive)

\* With no failures at all, every participant eventually decides.
NoFailureTermination ==
  [](coordinator.alive /\ \A i \in participants : participant[i].alive)
    => <>(\A i \in participants : participant[i].decision # "undecided")

-----------------------------------------------------------------------------
(* Invalid properties: these do NOT hold for ACP_SB *)

\* AC5 (termination): every participant that stays alive eventually decides.
\* This fails because the coordinator may die partway through the broadcast,
\* leaving participants that voted yes blocked forever.
AC5 ==
  <>(\A i \in participants :
       participant[i].alive => participant[i].decision # "undecided")

\* If all participants vote yes, they eventually all commit.
\* This fails when processes may fail.
AllYesImpliesCommit ==
  (\A i \in participants : participant[i].vote = "yes")
    => <>(\A i \in participants : participant[i].decision = "commit")

\* Every participant eventually decides, even dead ones.
AllDecide ==
  <>(\A i \in participants : participant[i].decision # "undecided")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInv /\ AC1 /\ AC2 /\ AC3_1)
THEOREM Spec => AC4
THEOREM Spec => AC3_2
THEOREM Spec => [](CommitImpliesCoordCommit /\ AbortImpliesNotCoordCommit)
=============================================================================
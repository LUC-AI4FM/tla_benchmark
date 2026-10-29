---------------------------- MODULE TwoPhaseCommit ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS participants,
          yes, no, undecided,
          commit, abort,
          waiting, notsent

participantsVal == {1, 2, 3}

VARIABLES participant,   \* participant state (vote, alive, decision)
          coordinator,   \* coordinator state
          msgs           \* in-flight messages (unreliable network)

vars == <<participant, coordinator, msgs>>

-----------------------------------------------------------------------------
\* Message universe (abstract unreliable per-recipient channels)

PrepareMsgs  == [type : {"prepare"}, to : participants]
VoteMsgs     == [type : {"vote"}, from : participants, val : {yes, no}]
DecisionMsgs == [type : {"decision"}, to : participants, val : {commit, abort}]
Messages     == PrepareMsgs \cup VoteMsgs \cup DecisionMsgs

ParticipantState ==
  [vote : {yes, no, undecided}, alive : BOOLEAN, decision : {undecided, commit, abort}]

CoordinatorState ==
  [request   : [participants -> BOOLEAN],
   vote      : [participants -> {waiting, yes, no}],
   broadcast : [participants -> {notsent, commit, abort}],
   decision  : {undecided, commit, abort},
   alive     : BOOLEAN]

TypeInv ==
  /\ participant \in [participants -> ParticipantState]
  /\ coordinator \in CoordinatorState
  /\ msgs \subseteq Messages

-----------------------------------------------------------------------------
Init ==
  /\ participant = [p \in participants |->
                      [vote |-> undecided, alive |-> TRUE, decision |-> undecided]]
  /\ coordinator = [request   |-> [p \in participants |-> FALSE],
                    vote      |-> [p \in participants |-> waiting],
                    broadcast |-> [p \in participants |-> notsent],
                    decision  |-> undecided,
                    alive     |-> TRUE]
  /\ msgs = {}

-----------------------------------------------------------------------------
\* Coordinator actions

\* Prepare phase: request (or re-request) a participant's vote
CoordSendPrepare(p) ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ coordinator.vote[p] = waiting
  /\ coordinator' = [coordinator EXCEPT !.request[p] = TRUE]
  /\ msgs' = msgs \cup {[type |-> "prepare", to |-> p]}
  /\ UNCHANGED participant

\* Vote received
CoordReceiveVote(p) ==
  /\ coordinator.alive
  /\ coordinator.vote[p] = waiting
  /\ \E m \in msgs :
        /\ m.type = "vote" /\ m.from = p
        /\ coordinator' = [coordinator EXCEPT !.vote[p] = m.val]
        /\ msgs' = msgs \ {m}
  /\ UNCHANGED participant

\* Decision: commit only if all voted yes; abort if any no (or on timeout)
CoordDecideCommit ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ \A p \in participants : coordinator.vote[p] = yes
  /\ coordinator' = [coordinator EXCEPT !.decision = commit]
  /\ UNCHANGED <<participant, msgs>>

CoordDecideAbort ==
  /\ coordinator.alive
  /\ coordinator.decision = undecided
  /\ ~(\A p \in participants : coordinator.vote[p] = yes)
  /\ coordinator' = [coordinator EXCEPT !.decision = abort]
  /\ UNCHANGED <<participant, msgs>>

\* Commit/abort phase: (re)broadcast the decision to a participant
CoordBroadcast(p) ==
  /\ coordinator.alive
  /\ coordinator.decision # undecided
  /\ participant[p].decision = undecided \/ coordinator.broadcast[p] = notsent
  /\ coordinator' = [coordinator EXCEPT !.broadcast[p] = coordinator.decision]
  /\ msgs' = msgs \cup {[type |-> "decision", to |-> p, val |-> coordinator.decision]}
  /\ UNCHANGED participant

\* Crash / recovery (decision, votes persisted on stable storage)
CoordCrash ==
  /\ coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = FALSE]
  /\ UNCHANGED <<participant, msgs>>

CoordRecover ==
  /\ ~coordinator.alive
  /\ coordinator' = [coordinator EXCEPT !.alive = TRUE]
  /\ UNCHANGED <<participant, msgs>>

-----------------------------------------------------------------------------
\* Participant actions

\* Receive prepare and vote (first time chooses yes/no; later re-sends vote)
ParticipantVote(p) ==
  /\ participant[p].alive
  /\ [type |-> "prepare", to |-> p] \in msgs
  /\ IF participant[p].vote = undecided
       THEN \E v \in {yes, no} :
              /\ participant' = [participant EXCEPT ![p].vote = v]
              /\ msgs' = (msgs \ {[type |-> "prepare", to |-> p]})
                           \cup {[type |-> "vote", from |-> p, val |-> v]}
       ELSE /\ msgs' = (msgs \ {[type |-> "prepare", to |-> p]})
                           \cup {[type |-> "vote", from |-> p, val |-> participant[p].vote]}
            /\ UNCHANGED participant
  /\ UNCHANGED coordinator

\* A participant that voted no may unilaterally abort
ParticipantLocalAbort(p) ==
  /\ participant[p].alive
  /\ participant[p].vote = no
  /\ participant[p].decision = undecided
  /\ participant' = [participant EXCEPT ![p].decision = abort]
  /\ UNCHANGED <<coordinator, msgs>>

\* Decision received and applied
ParticipantReceiveDecision(p) ==
  /\ participant[p].alive
  /\ \E m \in msgs :
        /\ m.type = "decision" /\ m.to = p
        /\ participant' = [participant EXCEPT ![p].decision = m.val]
        /\ msgs' = msgs \ {m}
  /\ UNCHANGED coordinator

ParticipantCrash(p) ==
  /\ participant[p].alive
  /\ participant' = [participant EXCEPT ![p].alive = FALSE]
  /\ UNCHANGED <<coordinator, msgs>>

ParticipantRecover(p) ==
  /\ ~participant[p].alive
  /\ participant' = [participant EXCEPT ![p].alive = TRUE]
  /\ UNCHANGED <<coordinator, msgs>>

-----------------------------------------------------------------------------
\* Network: message loss

LoseMsg ==
  /\ \E m \in msgs : msgs' = msgs \ {m}
  /\ UNCHANGED <<participant, coordinator>>

-----------------------------------------------------------------------------
progN ==
  \/ \E p \in participants :
        \/ CoordSendPrepare(p)
        \/ CoordReceiveVote(p)
        \/ CoordBroadcast(p)
        \/ ParticipantVote(p)
        \/ ParticipantLocalAbort(p)
        \/ ParticipantReceiveDecision(p)
        \/ ParticipantCrash(p)
        \/ ParticipantRecover(p)
  \/ CoordDecideCommit
  \/ CoordDecideAbort
  \/ CoordCrash
  \/ CoordRecover
  \/ LoseMsg

Spec == Init /\ [][progN]_vars

\* Weak liveness assumptions: crashed processes eventually recover,
\* messages are eventually delivered (strong fairness on receipt/retransmission).
Fairness ==
  /\ WF_vars(CoordRecover)
  /\ WF_vars(CoordDecideCommit)
  /\ WF_vars(CoordDecideAbort)
  /\ \A p \in participants :
        /\ WF_vars(ParticipantRecover(p))
        /\ SF_vars(CoordSendPrepare(p))
        /\ SF_vars(CoordReceiveVote(p))
        /\ SF_vars(CoordBroadcast(p))
        /\ SF_vars(ParticipantVote(p))
        /\ SF_vars(ParticipantReceiveDecision(p))

FairSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

Agreement ==
  \A p, q \in participants :
     (participant[p].decision # undecided /\ participant[q].decision # undecided)
        => participant[p].decision = participant[q].decision

Atomicity ==
  (\E p \in participants : participant[p].decision = commit)
     => \A q \in participants : participant[q].decision \in {undecided, commit}

ValidityCommit ==
  (\E p \in participants : participant[p].decision = commit)
     => \A q \in participants : participant[q].vote = yes

ValidityAbort ==
  (\E p \in participants : participant[p].vote = no)
     => \A q \in participants : participant[q].decision # commit

CoordConsistency ==
  /\ coordinator.decision = commit =>
        \A p \in participants : coordinator.vote[p] = yes
  /\ \A p \in participants :
        coordinator.vote[p] \in {yes, no} => coordinator.vote[p] = participant[p].vote
  /\ \A p \in participants :
        participant[p].decision # undecided /\ participant[p].vote # no
           => participant[p].decision = coordinator.decision

Safety == TypeInv /\ Agreement /\ Atomicity /\ ValidityCommit
            /\ ValidityAbort /\ CoordConsistency

\* Liveness

Termination ==
  <>(\A p \in participants : participant[p].decision # undecided)

CommitWhenAllYes ==
  (\A p \in participants : participant[p].vote = yes)
     ~> (\A p \in participants : participant[p].decision = commit)

=============================================================================
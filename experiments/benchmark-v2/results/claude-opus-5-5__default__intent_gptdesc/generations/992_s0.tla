---------------------------- MODULE NonBlockingAtomicCommit ----------------------------
(***************************************************************************)
(* Two-phase style atomic commitment: one coordinator and a set of        *)
(* participants. They communicate by asynchronous point-to-point messages  *)
(* and by a simple broadcast. A broadcast is a set of individual sends,    *)
(* one per recipient, so a crash of the sender part-way through loses the  *)
(* sends not yet made. Processes may crash, and a crashed process stays    *)
(* crashed. Messages addressed to a crashed process are never received,   *)
(* so they are in effect lost. Failure detection is abstract: an action    *)
(* may test directly whether another process has crashed.                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Participants          \* the finite, non-empty set of participants

ASSUME Participants # {} /\ IsFiniteSet(Participants)

Votes     == {"yes", "no"}
VoteVal   == Votes \cup {"none"}
Decisions == {"commit", "abort"}
DecVal    == Decisions \cup {"undecided"}

VARIABLES
  coordAlive,   \* TRUE iff the coordinator has not crashed
  pAlive,       \* pAlive[p] = TRUE iff participant p has not crashed
  vote,         \* vote[p] : the vote cast by p ("none" if p has not voted yet)
  pDecision,    \* pDecision[p] : the decision of participant p
  cDecision,    \* the decision of the coordinator
  reqSent,      \* the participants to which a vote request has been sent
  voteMsgs,     \* vote messages in transit to the coordinator
  coordVotes,   \* coordVotes[p] : p's vote as received by the coordinator
  bcastSent,    \* the participants to which the decision has been sent
  decMsgs       \* decision messages in transit to participants

vars == << coordAlive, pAlive, vote, pDecision, cDecision, reqSent,
           voteMsgs, coordVotes, bcastSent, decMsgs >>

-----------------------------------------------------------------------------
(* Legal state space *)

TypeOK ==
  /\ coordAlive \in BOOLEAN
  /\ pAlive \in [Participants -> BOOLEAN]
  /\ vote \in [Participants -> VoteVal]
  /\ pDecision \in [Participants -> DecVal]
  /\ cDecision \in DecVal
  /\ reqSent \subseteq Participants
  /\ voteMsgs \subseteq [from : Participants, v : Votes]
  /\ coordVotes \in [Participants -> VoteVal]
  /\ bcastSent \subseteq Participants
  /\ decMsgs \subseteq [to : Participants, d : Decisions]

Init ==
  /\ coordAlive = TRUE
  /\ pAlive = [p \in Participants |-> TRUE]
  /\ vote = [p \in Participants |-> "none"]
  /\ pDecision = [p \in Participants |-> "undecided"]
  /\ cDecision = "undecided"
  /\ reqSent = {}
  /\ voteMsgs = {}
  /\ coordVotes = [p \in Participants |-> "none"]
  /\ bcastSent = {}
  /\ decMsgs = {}

-----------------------------------------------------------------------------
(* Transitions. Each one is enabled independently; no ordering beyond the  *)
(* enabling conditions is imposed.                                         *)

\* The coordinator sends a vote request to p. This is one element of the
\* request broadcast.
CoordSendRequest(p) ==
  /\ coordAlive
  /\ cDecision = "undecided"
  /\ p \notin reqSent
  /\ reqSent' = reqSent \cup {p}
  /\ UNCHANGED << coordAlive, pAlive, vote, pDecision, cDecision,
                  voteMsgs, coordVotes, bcastSent, decMsgs >>

\* A live participant that has received a request replies with its vote.
ParticipantVote(p, v) ==
  /\ pAlive[p]
  /\ p \in reqSent
  /\ vote[p] = "none"
  /\ pDecision[p] = "undecided"
  /\ vote' = [vote EXCEPT ![p] = v]
  /\ voteMsgs' = voteMsgs \cup {[from |-> p, v |-> v]}
  /\ UNCHANGED << coordAlive, pAlive, pDecision, cDecision, reqSent,
                  coordVotes, bcastSent, decMsgs >>

\* The coordinator receives a vote. The vote is delivered even if its
\* sender has crashed since sending it.
CoordReceiveVote(m) ==
  /\ coordAlive
  /\ m \in voteMsgs
  /\ coordVotes' = [coordVotes EXCEPT ![m.from] = m.v]
  /\ voteMsgs' = voteMsgs \ {m}
  /\ UNCHANGED << coordAlive, pAlive, vote, pDecision, cDecision, reqSent,
                  bcastSent, decMsgs >>

\* The coordinator commits iff it has collected a yes vote from everyone.
CoordDecideCommit ==
  /\ coordAlive
  /\ cDecision = "undecided"
  /\ \A p \in Participants : coordVotes[p] = "yes"
  /\ cDecision' = "commit"
  /\ UNCHANGED << coordAlive, pAlive, vote, pDecision, reqSent, voteMsgs,
                  coordVotes, bcastSent, decMsgs >>

\* The coordinator aborts on a no vote, or when it detects that a
\* participant whose vote it has not collected has crashed.
CoordDecideAbort ==
  /\ coordAlive
  /\ cDecision = "undecided"
  /\ \/ \E p \in Participants : coordVotes[p] = "no"
     \/ \E p \in Participants : ~pAlive[p] /\ coordVotes[p] = "none"
  /\ cDecision' = "abort"
  /\ UNCHANGED << coordAlive, pAlive, vote, pDecision, reqSent, voteMsgs,
                  coordVotes, bcastSent, decMsgs >>

\* The coordinator sends its decision to p. This is one element of the
\* decision broadcast.
CoordBroadcast(p) ==
  /\ coordAlive
  /\ cDecision # "undecided"
  /\ p \notin bcastSent
  /\ bcastSent' = bcastSent \cup {p}
  /\ decMsgs' = decMsgs \cup {[to |-> p, d |-> cDecision]}
  /\ UNCHANGED << coordAlive, pAlive, vote, pDecision, cDecision, reqSent,
                  voteMsgs, coordVotes >>

\* A live participant receives the decision and adopts it if it is still
\* undecided.
ParticipantReceiveDecision(m) ==
  /\ m \in decMsgs
  /\ pAlive[m.to]
  /\ pDecision' = IF pDecision[m.to] = "undecided"
                    THEN [pDecision EXCEPT ![m.to] = m.d]
                    ELSE pDecision
  /\ decMsgs' = decMsgs \ {m}
  /\ UNCHANGED << coordAlive, pAlive, vote, cDecision, reqSent, voteMsgs,
                  coordVotes, bcastSent >>

\* Local abort. It is enabled only when an observed failure or no vote
\* makes a commit impossible:
\*   - p itself voted no;
\*   - some participant voted no (abstract knowledge);
\*   - the coordinator crashed before p cast a vote;
\*   - some participant crashed without voting.
ParticipantLocalAbort(p) ==
  /\ pAlive[p]
  /\ pDecision[p] = "undecided"
  /\ \/ vote[p] = "no"
     \/ \E q \in Participants : vote[q] = "no"
     \/ (~coordAlive /\ vote[p] = "none")
     \/ \E q \in Participants : ~pAlive[q] /\ vote[q] = "none"
  /\ pDecision' = [pDecision EXCEPT ![p] = "abort"]
  /\ UNCHANGED << coordAlive, pAlive, vote, cDecision, reqSent, voteMsgs,
                  coordVotes, bcastSent, decMsgs >>

\* Stop failures.
CoordCrash ==
  /\ coordAlive
  /\ coordAlive' = FALSE
  /\ UNCHANGED << pAlive, vote, pDecision, cDecision, reqSent, voteMsgs,
                  coordVotes, bcastSent, decMsgs >>

ParticipantCrash(p) ==
  /\ pAlive[p]
  /\ pAlive' = [pAlive EXCEPT ![p] = FALSE]
  /\ UNCHANGED << coordAlive, vote, pDecision, cDecision, reqSent, voteMsgs,
                  coordVotes, bcastSent, decMsgs >>

Next ==
  \/ \E p \in Participants : CoordSendRequest(p)
  \/ \E p \in Participants, v \in Votes : ParticipantVote(p, v)
  \/ \E m \in voteMsgs : CoordReceiveVote(m)
  \/ CoordDecideCommit
  \/ CoordDecideAbort
  \/ \E p \in Participants : CoordBroadcast(p)
  \/ \E m \in decMsgs : ParticipantReceiveDecision(m)
  \/ \E p \in Participants : ParticipantLocalAbort(p)
  \/ CoordCrash
  \/ \E p \in Participants : ParticipantCrash(p)

(* Fairness: every protocol step that stays enabled is eventually taken.   *)
(* Crashes carry no fairness requirement. A message to a live receiver     *)
(* is eventually delivered.                                                *)
Fairness ==
  /\ \A p \in Participants : WF_vars(CoordSendRequest(p))
  /\ \A p \in Participants : WF_vars(\E v \in Votes : ParticipantVote(p, v))
  /\ WF_vars(\E m \in voteMsgs : CoordReceiveVote(m))
  /\ WF_vars(CoordDecideCommit)
  /\ WF_vars(CoordDecideAbort)
  /\ \A p \in Participants : WF_vars(CoordBroadcast(p))
  /\ \A p \in Participants :
        WF_vars(\E m \in decMsgs : m.to = p /\ ParticipantReceiveDecision(m))
  /\ \A p \in Participants : WF_vars(ParticipantLocalAbort(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

Decided(p) == pDecision[p] # "undecided"

\* No two non-faulty participants decide differently.
AgreementNonFaulty ==
  \A p, q \in Participants :
     (pAlive[p] /\ pAlive[q] /\ Decided(p) /\ Decided(q))
        => pDecision[p] = pDecision[q]

\* A stronger form: agreement among all participants, crashed or not,
\* and with the coordinator.
Agreement ==
  /\ \A p, q \in Participants :
        (Decided(p) /\ Decided(q)) => pDecision[p] = pDecision[q]
  /\ \A p \in Participants :
        (Decided(p) /\ cDecision # "undecided") => pDecision[p] = cDecision

\* Commit only if every participant voted yes.
Validity ==
  /\ \A p \in Participants :
        pDecision[p] = "commit" => \A q \in Participants : vote[q] = "yes"
  /\ cDecision = "commit" => \A q \in Participants : vote[q] = "yes"

\* Every abort is explained by a no vote or by some crash.
AbortJustified ==
  LET Justification ==
        \/ \E q \in Participants : vote[q] = "no"
        \/ ~coordAlive
        \/ \E q \in Participants : ~pAlive[q]
  IN  /\ \A p \in Participants : pDecision[p] = "abort" => Justification
      /\ cDecision = "abort" => Justification

\* Once a decision is made, it never changes.
DecisionStable ==
  [][ /\ \A p \in Participants :
           Decided(p) => pDecision'[p] = pDecision[p]
      /\ cDecision # "undecided" => cDecision' = cDecision ]_vars

-----------------------------------------------------------------------------
(* Auxiliary invariants and stability properties used in reasoning *)

\* Crashes are permanent.
FaultStable ==
  [][ /\ ~coordAlive => ~coordAlive'
      /\ \A p \in Participants : ~pAlive[p] => ~pAlive'[p] ]_vars

\* A vote, once cast, never changes.
VoteStable ==
  [][ \A p \in Participants : vote[p] # "none" => vote'[p] = vote[p] ]_vars

\* What the coordinator and the channels know agrees with the actual votes.
VoteConsistency ==
  /\ \A p \in Participants : coordVotes[p] # "none" => coordVotes[p] = vote[p]
  /\ \A m \in voteMsgs : vote[m.from] = m.v
  /\ \A p \in Participants : vote[p] # "none" => p \in reqSent

\* Decision messages carry the coordinator's decision.
DecisionMsgConsistency ==
  /\ \A m \in decMsgs : m.d = cDecision
  /\ bcastSent # {} => cDecision # "undecided"

\* A participant that has not voted cannot be counted toward a commit.
NoCommitWithoutAllVotes ==
  (\E p \in Participants : vote[p] = "none") => cDecision # "commit"

Invariants ==
  /\ TypeOK
  /\ AgreementNonFaulty
  /\ Agreement
  /\ Validity
  /\ AbortJustified
  /\ VoteConsistency
  /\ DecisionMsgConsistency
  /\ NoCommitWithoutAllVotes

-----------------------------------------------------------------------------
(* Liveness properties *)

AllLiveDecided == \A p \in Participants : pAlive[p] => Decided(p)

\* If the coordinator does not fail, every live participant eventually
\* decides, whatever participant crashes happen.
\* (2PC can block if the coordinator crashes after collecting all yes votes,
\* so the property is conditioned on the coordinator staying up.)
LiveDecisionNoCoordFailure ==
  [](coordAlive) => <>(AllLiveDecided)

\* If no process ever fails, every participant eventually decides.
NoFailures == coordAlive /\ \A p \in Participants : pAlive[p]

TerminationNoFailures ==
  [](NoFailures) => <>(\A p \in Participants : Decided(p))

\* With no failures, if everyone votes yes the outcome is commit.
CommitWhenAllYes ==
  ([](NoFailures) /\ <>(\A p \in Participants : vote[p] = "yes"))
     => <>(\A p \in Participants : pDecision[p] = "commit")

\* With no failures, a no vote leads every participant to abort.
AbortWhenSomeNo ==
  ([](NoFailures) /\ <>(\E p \in Participants : vote[p] = "no"))
     => <>(\A p \in Participants : pDecision[p] = "abort")

THEOREM Spec => []Invariants
THEOREM Spec => DecisionStable /\ FaultStable /\ VoteStable
THEOREM Spec => LiveDecisionNoCoordFailure /\ TerminationNoFailures
THEOREM Spec => CommitWhenAllYes /\ AbortWhenSomeNo
=============================================================================
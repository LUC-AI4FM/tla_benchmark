------------------------------- MODULE NonBlockingAtomicCommit -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS Participant

ASSUME Participant # {} /\ IsFiniteSet(Participant)

Votes     == {"yes", "no"}
Outcomes  == {"commit", "abort"}
None      == "none"

VARIABLES
    vote,        \* vote[p] : the local vote of participant p
    alive,       \* alive[p] : FALSE once p has crashed (crash-stop model)
    sent,        \* participants whose vote has been broadcast (reliable broadcast)
    proposal,    \* proposal[p] : value p proposed to the underlying uniform consensus
    consensus,   \* the value chosen by the abstract uniform consensus
    decision     \* decision[p] : the final decision of participant p

vars == <<vote, alive, sent, proposal, consensus, decision>>

TypeOK ==
    /\ vote      \in [Participant -> Votes]
    /\ alive     \in [Participant -> BOOLEAN]
    /\ sent      \subseteq Participant
    /\ proposal  \in [Participant -> Outcomes \cup {None}]
    /\ consensus \in Outcomes \cup {None}
    /\ decision  \in [Participant -> Outcomes \cup {None}]

-----------------------------------------------------------------------------------------------

Init ==
    /\ vote      \in [Participant -> Votes]
    /\ alive     = [p \in Participant |-> TRUE]
    /\ sent      = {}
    /\ proposal  = [p \in Participant |-> None]
    /\ consensus = None
    /\ decision  = [p \in Participant |-> None]

\* Participant p broadcasts its vote to everybody.
SendVote(p) ==
    /\ alive[p]
    /\ p \notin sent
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<vote, alive, proposal, consensus, decision>>

\* Perfect failure detector: p suspects q iff q has crashed.
Suspected(q) == ~alive[q]

\* Conditions under which p proposes commit or abort.
CanProposeCommit ==
    /\ sent = Participant
    /\ \A q \in Participant : vote[q] = "yes"

CanProposeAbort ==
    \/ \E q \in sent : vote[q] = "no"
    \/ \E q \in Participant : Suspected(q) /\ q \notin sent

Propose(p) ==
    /\ alive[p]
    /\ p \in sent
    /\ proposal[p] = None
    /\ \/ CanProposeCommit /\ proposal' = [proposal EXCEPT ![p] = "commit"]
       \/ CanProposeAbort  /\ proposal' = [proposal EXCEPT ![p] = "abort"]
    /\ UNCHANGED <<vote, alive, sent, consensus, decision>>

\* Abstract uniform consensus: chooses exactly one proposed value, once.
ChooseConsensus ==
    /\ consensus = None
    /\ \E q \in Participant :
          /\ proposal[q] # None
          /\ consensus' = proposal[q]
    /\ UNCHANGED <<vote, alive, sent, proposal, decision>>

\* Participant p learns the consensus value and decides irrevocably.
Decide(p) ==
    /\ alive[p]
    /\ decision[p] = None
    /\ consensus # None
    /\ decision' = [decision EXCEPT ![p] = consensus]
    /\ UNCHANGED <<vote, alive, sent, proposal, consensus>>

\* Crash-stop failure of participant p.
Crash(p) ==
    /\ alive[p]
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<vote, sent, proposal, consensus, decision>>

\* Termination: every live participant has decided.
Done ==
    /\ \A p \in Participant : alive[p] => decision[p] # None
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Participant :
          \/ SendVote(p)
          \/ Propose(p)
          \/ Decide(p)
          \/ Crash(p)
    \/ ChooseConsensus
    \/ Done

Fairness ==
    /\ \A p \in Participant :
          /\ WF_vars(SendVote(p))
          /\ WF_vars(Propose(p))
          /\ WF_vars(Decide(p))
    /\ WF_vars(ChooseConsensus)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------------
\* Safety properties

\* Agreement (uniform): no two participants decide differently.
Agreement ==
    \A p, q \in Participant :
        (decision[p] # None /\ decision[q] # None) => decision[p] = decision[q]

\* Commit only if every participant voted yes.
CommitValidity ==
    \A p \in Participant :
        decision[p] = "commit" => \A q \in Participant : vote[q] = "yes"

\* If any participant voted no, any decision is abort.
AbortValidity ==
    (\E q \in Participant : vote[q] = "no") =>
        \A p \in Participant : decision[p] \in {None, "abort"}

\* If all voted yes and no failures occurred, any decision is commit.
NoFailureCommitValidity ==
    ( /\ \A q \in Participant : vote[q] = "yes"
      /\ \A q \in Participant : alive[q] )
    => \A p \in Participant : decision[p] \in {None, "commit"}

Safety ==
    /\ TypeOK
    /\ Agreement
    /\ CommitValidity
    /\ AbortValidity
    /\ NoFailureCommitValidity

\* Irrevocability: decisions never change once made.
Irrevocability ==
    [][\A p \in Participant :
          decision[p] # None => decision'[p] = decision[p]]_vars

CommitStable ==
    \A p \in Participant : [](decision[p] = "commit" => [](decision[p] = "commit"))

AbortStable ==
    \A p \in Participant : [](decision[p] = "abort" => [](decision[p] = "abort"))

\* Votes never change.
VoteStable == [][vote' = vote]_vars

-----------------------------------------------------------------------------------------------
\* Liveness properties

\* Termination (non-blocking): every non-failed participant eventually decides.
Termination ==
    \A p \in Participant : <>(decision[p] # None \/ ~alive[p])

\* If everyone votes yes and nobody ever fails, the outcome is eventually commit.
CommitLiveness ==
    ( /\ \A q \in Participant : vote[q] = "yes"
      /\ [](\A q \in Participant : alive[q]) )
    => <>(\A p \in Participant : decision[p] = "commit")

-----------------------------------------------------------------------------------------------
\* Symmetry among participants for model checking

Symmetry == Permutations(Participant)

THEOREM Spec => []Safety
THEOREM Spec => Irrevocability
THEOREM Spec => Termination
===============================================================================================
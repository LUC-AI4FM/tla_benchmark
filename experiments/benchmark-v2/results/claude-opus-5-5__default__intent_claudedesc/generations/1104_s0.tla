---------------------------- MODULE NonBlockingAtomicCommit ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

Procs == 1..N

Votes     == {"yes", "no"}
Decisions == {"commit", "abort"}
Messages  == [src : Procs, val : Votes]

VARIABLES
    pc,           \* local control state of each process
    vote,         \* vote cast by each process ("none" before voting)
    msgs,         \* set of broadcast vote messages (reliable broadcast)
    rcvd,         \* rcvd[p] : set of vote messages delivered to p
    suspected,    \* suspected[p] : processes p's failure detector reports as crashed
    crashed,      \* set of processes that have crashed
    proposal,     \* value each process proposes to the underlying consensus
    fdAtPropose,  \* TRUE iff p had detected a failure when it proposed
    consensus,    \* value chosen by the underlying (uniform) consensus abstraction
    decision      \* final decision of each process ("none" before deciding)

vars == << pc, vote, msgs, rcvd, suspected, crashed, proposal,
           fdAtPropose, consensus, decision >>

-----------------------------------------------------------------------------
\* Derived counters: number of Yes / No votes received by p

nYes(p) == Cardinality({m \in rcvd[p] : m.val = "yes"})
nNo(p)  == Cardinality({m \in rcvd[p] : m.val = "no"})

\* p has either received a vote from q or its failure detector suspects q
HeardFromAll(p) ==
    \A q \in Procs : (\E m \in rcvd[p] : m.src = q) \/ q \in suspected[p]

-----------------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Procs -> {"init", "voted", "proposed", "decided"}]
    /\ vote \in [Procs -> Votes \cup {"none"}]
    /\ msgs \subseteq Messages
    /\ rcvd \in [Procs -> SUBSET Messages]
    /\ suspected \in [Procs -> SUBSET Procs]
    /\ crashed \subseteq Procs
    /\ proposal \in [Procs -> Decisions \cup {"none"}]
    /\ fdAtPropose \in [Procs -> BOOLEAN]
    /\ consensus \in Decisions \cup {"none"}
    /\ decision \in [Procs -> Decisions \cup {"none"}]

Init ==
    /\ pc = [p \in Procs |-> "init"]
    /\ vote = [p \in Procs |-> "none"]
    /\ msgs = {}
    /\ rcvd = [p \in Procs |-> {}]
    /\ suspected = [p \in Procs |-> {}]
    /\ crashed = {}
    /\ proposal = [p \in Procs |-> "none"]
    /\ fdAtPropose = [p \in Procs |-> FALSE]
    /\ consensus = "none"
    /\ decision = [p \in Procs |-> "none"]

-----------------------------------------------------------------------------
\* Voting phase: p casts its vote and broadcasts it to all participants
Vote(p, v) ==
    /\ p \notin crashed
    /\ pc[p] = "init"
    /\ vote' = [vote EXCEPT ![p] = v]
    /\ msgs' = msgs \cup {[src |-> p, val |-> v]}
    /\ pc' = [pc EXCEPT ![p] = "voted"]
    /\ UNCHANGED << rcvd, suspected, crashed, proposal, fdAtPropose,
                    consensus, decision >>

\* Message exchange: p receives a broadcast vote
Receive(p, m) ==
    /\ p \notin crashed
    /\ pc[p] \in {"init", "voted"}
    /\ m \in msgs \ rcvd[p]
    /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED << pc, vote, msgs, suspected, crashed, proposal,
                    fdAtPropose, consensus, decision >>

\* Perfect failure detector: p detects that q has crashed
Detect(p, q) ==
    /\ p \notin crashed
    /\ pc[p] \in {"init", "voted"}
    /\ q \in crashed \ suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED << pc, vote, msgs, rcvd, crashed, proposal,
                    fdAtPropose, consensus, decision >>

\* Once p has heard from (or suspects) every participant it proposes:
\* commit only if N Yes votes were received and no failure was detected.
Propose(p) ==
    /\ p \notin crashed
    /\ pc[p] = "voted"
    /\ HeardFromAll(p)
    /\ proposal' = [proposal EXCEPT ![p] =
                      IF nYes(p) = N /\ nNo(p) = 0 /\ suspected[p] = {}
                        THEN "commit" ELSE "abort"]
    /\ fdAtPropose' = [fdAtPropose EXCEPT ![p] = (suspected[p] # {})]
    /\ pc' = [pc EXCEPT ![p] = "proposed"]
    /\ UNCHANGED << vote, msgs, rcvd, suspected, crashed, consensus, decision >>

\* Abstract uniform consensus (made non-blocking by the failure detector):
\* decides once every non-crashed process has proposed; the result is one of
\* the proposed values (commit iff every proposal is commit).
ConsensusDecide ==
    /\ consensus = "none"
    /\ \A q \in Procs : q \in crashed \/ proposal[q] # "none"
    /\ \E q \in Procs : proposal[q] # "none"
    /\ consensus' = IF \A q \in Procs : proposal[q] \in {"none", "commit"}
                      THEN "commit" ELSE "abort"
    /\ UNCHANGED << pc, vote, msgs, rcvd, suspected, crashed, proposal,
                    fdAtPropose, decision >>

\* Decision: p learns the consensus value and decides (at most once)
Decide(p) ==
    /\ p \notin crashed
    /\ pc[p] = "proposed"
    /\ consensus # "none"
    /\ decision[p] = "none"
    /\ decision' = [decision EXCEPT ![p] = consensus]
    /\ pc' = [pc EXCEPT ![p] = "decided"]
    /\ UNCHANGED << vote, msgs, rcvd, suspected, crashed, proposal,
                    fdAtPropose, consensus >>

\* A process may crash at any time
Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED << pc, vote, msgs, rcvd, suspected, proposal,
                    fdAtPropose, consensus, decision >>

Next ==
    \/ \E p \in Procs, v \in Votes : Vote(p, v)
    \/ \E p \in Procs, m \in Messages : Receive(p, m)
    \/ \E p, q \in Procs : Detect(p, q)
    \/ \E p \in Procs : Propose(p)
    \/ ConsensusDecide
    \/ \E p \in Procs : Decide(p)
    \/ \E p \in Procs : Crash(p)

Fairness ==
    /\ \A p \in Procs :
         /\ WF_vars(\E v \in Votes : Vote(p, v))
         /\ WF_vars(\E m \in Messages : Receive(p, m))
         /\ WF_vars(\E q \in Procs : Detect(p, q))
         /\ WF_vars(Propose(p))
         /\ WF_vars(Decide(p))
    /\ WF_vars(ConsensusDecide)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

\* Agreement: no two processes decide differently
Agreement ==
    \A p, q \in Procs :
        (decision[p] # "none" /\ decision[q] # "none") => decision[p] = decision[q]

\* Validity (commit): commit only if all voted Yes and no failure was detected
CommitValidity ==
    \A p \in Procs :
        decision[p] = "commit" =>
            /\ \A q \in Procs : vote[q] = "yes"
            /\ \A q \in Procs : ~fdAtPropose[q]

\* Validity (abort): any No vote or any detected failure forces abort
AbortValidity ==
    (\E q \in Procs : vote[q] = "no" \/ fdAtPropose[q]) =>
        \A p \in Procs : decision[p] \in {"none", "abort"}

\* Integrity: each process decides at most once
IntegrityInv ==
    \A p \in Procs : (decision[p] # "none") <=> (pc[p] = "decided")

Integrity ==
    [][\A p \in Procs : decision[p] # "none" => decision'[p] = decision[p]]_vars

\* Liveness: every correct process eventually decides (non-blocking)
Termination ==
    <>[](\A p \in Procs : p \in crashed \/ decision[p] # "none")

THEOREM Spec => [](TypeOK /\ Agreement /\ CommitValidity /\ AbortValidity /\ IntegrityInv)
THEOREM Spec => Integrity
THEOREM Spec => Termination
=============================================================================
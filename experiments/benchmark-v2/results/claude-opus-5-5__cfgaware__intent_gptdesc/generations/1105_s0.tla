------------------------------ MODULE NBAC ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Proc == 1 .. N

Votes == {"YES", "NO"}

PcValues == {"INIT", "SENT", "COMMIT", "ABORT", "CRASH"}

Outcomes == {"NONE", "COMMIT", "ABORT"}

VARIABLES
    vote,       \* vote[i]: the initial binary vote of process i (fixed)
    pc,         \* pc[i]: local control state of process i
    sent,       \* set of processes that have broadcast their vote
    rcvd,       \* rcvd[i]: set of processes whose vote message i has received
    suspected,  \* set of processes suspected by the (perfect) failure detector
    outcome     \* abstract agreed outcome (underlying agreement object)

vars == << vote, pc, sent, rcvd, suspected, outcome >>

-------------------------------------------------------------------------
\* Type invariant

TypeOK ==
    /\ vote \in [Proc -> Votes]
    /\ pc \in [Proc -> PcValues]
    /\ sent \subseteq Proc
    /\ Cardinality(sent) <= N
    /\ rcvd \in [Proc -> SUBSET Proc]
    /\ \A i \in Proc : Cardinality(rcvd[i]) <= N
    /\ \A i \in Proc : rcvd[i] \subseteq sent
    /\ suspected \subseteq Proc
    /\ Cardinality(suspected) <= N
    /\ suspected = { i \in Proc : pc[i] = "CRASH" }
    /\ outcome \in Outcomes

-------------------------------------------------------------------------
\* Initial states: any distribution of votes, nobody has sent, crashed,
\* or been suspected.

Init ==
    /\ vote \in [Proc -> Votes]
    /\ pc = [i \in Proc |-> "INIT"]
    /\ sent = {}
    /\ rcvd = [i \in Proc |-> {}]
    /\ suspected = {}
    /\ outcome = "NONE"

-------------------------------------------------------------------------
\* Actions

\* Process i broadcasts its vote exactly once.
Send(i) ==
    /\ pc[i] = "INIT"
    /\ pc' = [pc EXCEPT ![i] = "SENT"]
    /\ sent' = sent \cup {i}
    /\ UNCHANGED << vote, rcvd, suspected, outcome >>

\* The vote message of sender j is delivered to the noncrashed recipient i.
Deliver(i, j) ==
    /\ pc[i] # "CRASH"
    /\ j \in sent
    /\ j \notin rcvd[i]
    /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup {j}]
    /\ UNCHANGED << vote, pc, sent, suspected, outcome >>

\* Process i crashes; it is immediately and permanently suspected.
Crash(i) ==
    /\ pc[i] # "CRASH"
    /\ pc' = [pc EXCEPT ![i] = "CRASH"]
    /\ suspected' = suspected \cup {i}
    /\ UNCHANGED << vote, sent, rcvd, outcome >>

\* Local knowledge based conditions
CanCommit(i) ==
    \A j \in Proc : j \in rcvd[i] /\ vote[j] = "YES"

CanAbort(i) ==
    \/ \E j \in rcvd[i] : vote[j] = "NO"
    \/ \E j \in suspected : j \notin rcvd[i]

\* Process i decides based on its local knowledge; the decision goes
\* through an abstract agreement object (first proposal wins).
Decide(i) ==
    /\ pc[i] = "SENT"
    /\ CanCommit(i) \/ CanAbort(i)
    /\ IF outcome # "NONE"
         THEN /\ pc' = [pc EXCEPT ![i] = outcome]
              /\ UNCHANGED outcome
         ELSE \/ /\ CanCommit(i)
                 /\ outcome' = "COMMIT"
                 /\ pc' = [pc EXCEPT ![i] = "COMMIT"]
              \/ /\ CanAbort(i)
                 /\ outcome' = "ABORT"
                 /\ pc' = [pc EXCEPT ![i] = "ABORT"]
    /\ UNCHANGED << vote, sent, rcvd, suspected >>

Next ==
    \/ \E i \in Proc : Send(i)
    \/ \E i, j \in Proc : Deliver(i, j)
    \/ \E i \in Proc : Crash(i)
    \/ \E i \in Proc : Decide(i)

\* Weak fairness: noncrashed processes eventually send and decide,
\* messages from noncrashed senders are eventually delivered.
Fairness ==
    /\ \A i \in Proc : WF_vars(Send(i))
    /\ \A i \in Proc : WF_vars(Decide(i))
    /\ \A i, j \in Proc : WF_vars(Deliver(i, j) /\ pc[j] # "CRASH")

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------
\* Correctness properties

\* Agreement: no process commits while another aborts.
AgrrLtl ==
    [](~(\E i, j \in Proc : pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

\* Abort validity: if some process votes NO, nobody commits.
AbortValidityLtl ==
    (\E i \in Proc : vote[i] = "NO")
        => [](\A i \in Proc : pc[i] # "COMMIT")

\* Commit validity: if all vote YES and no process crashes / is
\* suspected, nobody aborts.
CommitValidityLtl ==
    ((\A i \in Proc : vote[i] = "YES") /\ suspected = {})
        => []((suspected = {} /\ \A i \in Proc : pc[i] # "CRASH")
                => (\A i \in Proc : pc[i] # "ABORT"))

\* Termination: once crashes stop (there are finitely many) and the
\* failure detector never suspects noncrashed processes, every
\* noncrashed process eventually decides.
TerminationLtl ==
    (<>[](\A i \in Proc : (i \in suspected) <=> (pc[i] = "CRASH")))
        => <>(\A i \in Proc : pc[i] \in {"COMMIT", "ABORT", "CRASH"})

=========================================================================
------------------------------- MODULE DistributedLedger -------------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Nodes,  \* Set of nodes
    InitCommits  \* Initial set of committed transactions across all nodes

VARIABLES 
    commits,  \* commits[n] is the sequence of committed transactions at node n
    proposals  \* proposals[n] is the set of proposed but not yet committed transactions at node n

Init == /\ commits = [n \in Nodes |-> <<>>]
        /\ proposals = [n \in Nodes |-> {}]
        /\ \/ InitCommits = {}
           \/ \E n \in Nodes : InitCommits = commits[n]

Next ==
    \/ \E n \in Nodes, t \notin (Union {commits[m] : m \in Nodes}) :
         proposals' = [proposals EXCEPT ![n] = proposals[n] \cup {t}]
    \/ \E n \in Nodes, t \in proposals[n] :
         /\ commits' = [commits EXCEPT ![n] = Append(commits[n], t)]
         /\ proposals' = [proposals EXCEPT ![n] = proposals[n] \ {t}]
    \/ \E n1, n2 \in Nodes, t \in commits[n1] \ commits[n2] :
         commits' = [commits EXCEPT ![n2] = Append(commits[n2], t)]

Spec ==
    /\ Init
    /\ [][Next]_<<commits, proposals>>
    /\ WF_next(<<commits, proposals>>)

\* Safety properties

\* Once a transaction is reported committed, its effects are never lost and subsequent reads that observe that commit must not contradict it.
Safety1 == \A n \in Nodes, t \in commits[n] : \A m \in Nodes : t \notin commits[m] => UNCHANGED commits[m]

\* Monotonic visibility
MonotonicVisibility ==
    \A n \in Nodes :
        \A i, j \in 1..Len(commits[n]) : i <= j =>
            /\ commits[n][i] \in commits[n][j]
            /\ (\E k \leq j : commits[n][k] = commits[n][i])

\* Consistency across nodes
Consistency ==
    \A t \in Union {commits[n] : n \in Nodes} :
        \A n \in Nodes :
            \/ t \notin commits[n]
            \/ (\E m \in Nodes, k \leq Len(commits[m]) : commits[m][k] = t)

\* Liveness properties

\* Eventual visibility
EventualVisibility ==
    \A t \in Union {proposals[n] : n \in Nodes} :
        WF_next(<<commits>>) => <>[](\E n \in Nodes : t \in commits[n])

\* Internal consistency of observed sets with the ordering of committed transactions
InternalConsistency ==
    \A n \in Nodes, i, j \in 1..Len(commits[n]) :
        i <= j => commits[n][i] \in commits[n][j]

=============================================================================
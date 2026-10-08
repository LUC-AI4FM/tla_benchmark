---------------------------- MODULE MCSpecMultiNodeReadsAlt ----------------------------

CONSTANTS 
    Nodes,  \* The set of all nodes in the system
    Transactions  \* The set of all possible transactions

VARIABLES 
    committedAt,  \* committedAt[n] is the sequence of transactions committed at node n
    proposedAt,   \* proposedAt[n] is the set of transactions proposed but not yet committed at node n
    visibleAt     \* visibleAt[n] is the set of transaction identifiers visible to reads at node n

\* Initial predicate: Some nodes may start with some transactions already committed.
Init == 
    /\ committedAt = [n \in Nodes |-> <<>>]
    /\ proposedAt = [n \in Nodes |-> {}]
    /\ visibleAt = [n \in Nodes |-> {}]

\* Propose a transaction at a node
Propose(n, tx) ==
    /\ n \in Nodes
    /\ tx \notin committedAt[n] 
    /\ tx \notin proposedAt[n]
    /\ proposedAt' = [proposedAt EXCEPT ![n] = proposedAt[n] \cup {tx}]
    /\ UNCHANGED <<committedAt, visibleAt>>

\* Commit a transaction at a node
Commit(n, tx) ==
    /\ n \in Nodes
    /\ tx \in proposedAt[n]
    /\ committedAt' = [committedAt EXCEPT ![n] = Append(committedAt[n], tx)]
    /\ proposedAt' = [proposedAt EXCEPT ![n] = proposedAt[n] \ {tx}]
    /\ visibleAt' = [visibleAt EXCEPT ![n] = visibleAt[n] \cup {tx}]

\* Read transactions at a node
Read(n) ==
    /\ n \in Nodes
    /\ visibleAt' = [visibleAt EXCEPT ![n] = UNION {committedAt[m] : m \in Nodes}]
    /\ UNCHANGED <<proposedAt, committedAt>>

\* Next state relation
Next == 
    \/ \E n \in Nodes, tx \in Transactions : Propose(n, tx)
    \/ \E n \in Nodes, tx \in Transactions : Commit(n, tx)
    \/ \E n \in Nodes : Read(n)

\* Specification
Spec == Init /\ [][Next]_<<committedAt, proposedAt, visibleAt>>

\* Safety property: Once a transaction is committed, it remains committed.
Safety ==
    \A n \in Nodes, tx \in Transactions :
        \/ tx \notin committedAt[n]
        \/ \A m \in Nodes : tx \in committedAt[m] => tx \in visibleAt[m]

\* Monotonic visibility property: Reads observe a non-decreasing set of transactions.
MonotonicVisibility ==
    \A n \in Nodes, t1, t2 \in _<<committedAt, proposedAt, visibleAt>> :
        /\ t1 < t2
        => visibleAt[n]@t1 \subseteq visibleAt[n]@t2

\* Consistency across nodes: If a transaction is committed system-wide, it becomes visible to all nodes.
Consistency ==
    \A tx \in Transactions, n \in Nodes :
        (\E m \in Nodes : tx \in committedAt[m])
        => \A t \in _<<committedAt, proposedAt, visibleAt>> :
            tx \in committedAt[m]@t
            => tx \in visibleAt[n]@t

\* Internal consistency of observed transactions: Reads observe a consistent prefix of committed transactions.
InternalConsistency ==
    \A n \in Nodes, t \in _<<committedAt, proposedAt, visibleAt>> :
        /\ LET vis = visibleAt[n]@t
           IN \A tx1, tx2 \in Transactions :
                /\ tx1 \in vis
                /\ tx2 \in committedAt[n]@t
                /\ tx1 < tx2
                => tx2 \in vis

\* Complete specification with properties
CompleteSpec == Spec /\ []Safety /\ []MonotonicVisibility /\ []Consistency /\ []InternalConsistency

=============================================================================
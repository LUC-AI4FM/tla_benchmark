------------------------------ MODULE DistributedLedger ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,          \* set of ledger nodes, each maintaining a local branch
    Txns,           \* set of transaction identifiers
    InitLog         \* sequence of transactions already committed initially

ASSUME NodesNonEmpty == Nodes # {}
ASSUME InitLogType   == InitLog \in Seq(Txns)
ASSUME InitLogNoDup  == \A i, j \in 1..Len(InitLog) : i # j => InitLog[i] # InitLog[j]

NoNode == CHOOSE x : x \notin Nodes

Range(s) == { s[i] : i \in DOMAIN s }

VARIABLES
    status,     \* status[t] \in {"idle","proposed","committed","aborted"}
    origin,     \* origin[t] : node that accepted transaction t (or NoNode)
    log,        \* the systemwide commit order (sequence of committed transactions)
    known,      \* known[n] : length of the committed-log prefix visible at node n
    lastObs     \* lastObs[n] : set of txn ids returned by the latest read at node n

vars == <<status, origin, log, known, lastObs>>

Statuses == {"idle", "proposed", "committed", "aborted"}

\* Committed transactions visible on node n's local branch
VisibleAt(n) == Range(SubSeq(log, 1, known[n]))

-----------------------------------------------------------------------------
TypeOK ==
    /\ status  \in [Txns -> Statuses]
    /\ origin  \in [Txns -> Nodes \cup {NoNode}]
    /\ log     \in Seq(Txns)
    /\ known   \in [Nodes -> 0..Len(log)]
    /\ lastObs \in [Nodes -> SUBSET Txns]

-----------------------------------------------------------------------------
Init ==
    /\ log    = InitLog
    /\ status = [t \in Txns |-> IF t \in Range(InitLog) THEN "committed" ELSE "idle"]
    /\ origin = [t \in Txns |-> NoNode]
    \* initially committed txns are visible on one or more branches (some prefix elsewhere)
    /\ known \in { f \in [Nodes -> 0..Len(InitLog)] :
                      \E n \in Nodes : f[n] = Len(InitLog) }
    /\ lastObs = [n \in Nodes |-> Range(SubSeq(InitLog, 1, known[n]))]

\* A node independently accepts a new transaction
Propose(n, t) ==
    /\ status[t] = "idle"
    /\ status' = [status EXCEPT ![t] = "proposed"]
    /\ origin' = [origin EXCEPT ![t] = n]
    /\ UNCHANGED <<log, known, lastObs>>

\* Processing of a proposed transaction results in a commit: it is appended to the
\* global commit order and becomes visible on the accepting node's branch.
Commit(t) ==
    /\ status[t] = "proposed"
    /\ status' = [status EXCEPT ![t] = "committed"]
    /\ log'    = Append(log, t)
    /\ known'  = [known EXCEPT ![origin[t]] = Len(log) + 1]
    /\ UNCHANGED <<origin, lastObs>>

\* Processing of a proposed transaction results in it not being committed
Abort(t) ==
    /\ status[t] = "proposed"
    /\ status' = [status EXCEPT ![t] = "aborted"]
    /\ UNCHANGED <<origin, log, known, lastObs>>

\* Commit status is communicated to node n: its branch learns the next committed txn
Sync(n) ==
    /\ known[n] < Len(log)
    /\ known' = [known EXCEPT ![n] = known[n] + 1]
    /\ UNCHANGED <<status, origin, log, lastObs>>

\* A read on node n's local branch returns the committed prefix visible there
Read(n) ==
    /\ lastObs' = [lastObs EXCEPT ![n] = VisibleAt(n)]
    /\ UNCHANGED <<status, origin, log, known>>

Next ==
    \/ \E n \in Nodes, t \in Txns : Propose(n, t)
    \/ \E t \in Txns : Commit(t)
    \/ \E t \in Txns : Abort(t)
    \/ \E n \in Nodes : Sync(n)
    \/ \E n \in Nodes : Read(n)

Fairness ==
    /\ \A n \in Nodes : WF_vars(Sync(n))
    /\ \A n \in Nodes : WF_vars(Read(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* SAFETY INVARIANTS

\* The commit log contains no duplicates
LogNoDup == \A i, j \in 1..Len(log) : i # j => log[i] # log[j]

\* Committed status corresponds exactly to membership in the durable commit log
CommittedInLog == \A t \in Txns : (status[t] = "committed") <=> (t \in Range(log))

\* Reads only observe committed transactions, and only those visible at that node
ReadsObserveCommitted ==
    \A n \in Nodes : lastObs[n] \subseteq VisibleAt(n)

\* Every read result is exactly a prefix of the committed history
ReadIsPrefix ==
    \A n \in Nodes : \E k \in 0..known[n] : lastObs[n] = Range(SubSeq(log, 1, k))

\* No observing a later commit while missing an earlier committed predecessor
OrderConsistentReads ==
    \A n \in Nodes : \A i, j \in 1..Len(log) :
        (i < j /\ log[j] \in lastObs[n]) => log[i] \in lastObs[n]

SafetyInv ==
    /\ TypeOK
    /\ LogNoDup
    /\ CommittedInLog
    /\ ReadsObserveCommitted
    /\ ReadIsPrefix
    /\ OrderConsistentReads

-----------------------------------------------------------------------------
\* ACTION (TEMPORAL) SAFETY PROPERTIES

\* Durability: once committed, a transaction stays committed and the log is never truncated
Durability ==
    [][ /\ \A t \in Txns : status[t] = "committed" => status'[t] = "committed"
        /\ Len(log) <= Len(log')
        /\ SubSeq(log', 1, Len(log)) = log ]_vars

\* Monotonic visibility: a node's branch never rolls back
MonotonicBranch ==
    [][ \A n \in Nodes : known[n] <= known'[n] ]_vars

\* Monotonic reads: a later read on the same node observes at least what an earlier one did
MonotonicReads ==
    [][ \A n \in Nodes : lastObs[n] \subseteq lastObs'[n] ]_vars

\* A read following a commit on the same node observes that commit
ReadAfterCommit ==
    [][ \A n \in Nodes :
          Read(n) => \A t \in Txns :
              (status[t] = "committed" /\ origin[t] = n) => t \in lastObs'[n] ]_vars

-----------------------------------------------------------------------------
\* LIVENESS: eventual visibility across all nodes

EventualVisibility ==
    \A t \in Txns, n \in Nodes :
        (status[t] = "committed") ~> (t \in VisibleAt(n))

EventualReadVisibility ==
    \A t \in Txns, n \in Nodes :
        (status[t] = "committed") ~> (t \in lastObs[n])

-----------------------------------------------------------------------------
THEOREM Spec => []SafetyInv
THEOREM Spec => Durability /\ MonotonicBranch /\ MonotonicReads /\ ReadAfterCommit
THEOREM Spec => EventualVisibility /\ EventualReadVisibility

=============================================================================
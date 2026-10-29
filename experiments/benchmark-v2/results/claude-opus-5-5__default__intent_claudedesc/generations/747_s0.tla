------------------------- MODULE CheckpointCoordination -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Node,        \* set of nodes in the cluster
    Timeout,     \* logical lease timeout (ticks)
    MaxLogLen    \* bound on replicated log length (for model checking)

ASSUME /\ Timeout \in Nat \ {0}
       /\ MaxLogLen \in Nat
       /\ Node # {}

NoNode == CHOOSE x : x \notin Node

VARIABLES
    up,             \* up[n] : node n is alive
    link,           \* link[<<n,m>>] : directed link n -> m is working
    leader,         \* current leader or NoNode
    chosen,         \* the consensus-decided (committed) log
    log,            \* log[n] : node n's locally persisted log (prefix of chosen)
    taking,         \* taking[n] : node n is currently taking a checkpoint (volatile)
    ckpt,           \* ckpt[n] : lease position of n's last completed checkpoint (persistent)
    pendingReport,  \* pendingReport[n] : lease pos of completed checkpoint not yet reported (volatile)
    timer,          \* logical timeout counter for the latest lease
    expired,        \* set of lease positions that have timed out
    latestCkptLen   \* log length covered by the latest available checkpoint

vars == <<up, link, leader, chosen, log, taking, ckpt, pendingReport,
          timer, expired, latestCkptLen>>

-----------------------------------------------------------------------------
\* Helpers

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

Entries == [type : {"lease", "done"}, node : Node, pos : 1..MaxLogLen]

Majority == {Q \in SUBSET Node : 2 * Cardinality(Q) > Cardinality(Node)}

Connected(n, m) == (n = m) \/ (link[<<n, m>>] /\ link[<<m, n>>])

Reachable(n) == {m \in Node : up[m] /\ Connected(n, m)}

HasQuorum(n) == Reachable(n) \in Majority

\* Position of the last lease entry in a log (0 if none)
LastLeasePos(s) ==
    IF \E i \in 1..Len(s) : s[i].type = "lease"
    THEN CHOOSE i \in 1..Len(s) :
            /\ s[i].type = "lease"
            /\ \A j \in (i+1)..Len(s) : s[j].type # "lease"
    ELSE 0

LeaseHolder(s) == IF LastLeasePos(s) > 0 THEN s[LastLeasePos(s)].node ELSE NoNode

\* The holder of the last lease has reported completion
DoneRecorded(s) ==
    /\ LastLeasePos(s) > 0
    /\ \E i \in 1..Len(s) : s[i].type = "done" /\ s[i].pos = LastLeasePos(s)

\* The leader has a (live) lease recorded
LeaderHasLease ==
    /\ leader # NoNode
    /\ LastLeasePos(log[leader]) > 0
    /\ ~DoneRecorded(log[leader])
    /\ LastLeasePos(log[leader]) \notin expired

\* A new lease may be granted
LeaseReplaceable(s) ==
    \/ LastLeasePos(s) = 0
    \/ LastLeasePos(s) \in expired
    \/ DoneRecorded(s)

HeldLeasePos(n) == LastLeasePos(log[n])

HeldLeaseExpired(n) == HeldLeasePos(n) > 0 /\ HeldLeasePos(n) \in expired

\* Node n believes it is authorized to take a checkpoint
CanCheckpoint(n) ==
    /\ up[n]
    /\ n # leader
    /\ HeldLeasePos(n) > 0
    /\ log[n][HeldLeasePos(n)].node = n
    /\ HeldLeasePos(n) \notin expired
    /\ ckpt[n] < HeldLeasePos(n)

-----------------------------------------------------------------------------
TypeOK ==
    /\ up \in [Node -> BOOLEAN]
    /\ link \in [Node \X Node -> BOOLEAN]
    /\ leader \in Node \cup {NoNode}
    /\ chosen \in Seq(Entries)
    /\ Len(chosen) <= MaxLogLen
    /\ log \in [Node -> Seq(Entries)]
    /\ taking \in [Node -> BOOLEAN]
    /\ ckpt \in [Node -> 0..MaxLogLen]
    /\ pendingReport \in [Node -> 0..MaxLogLen]
    /\ timer \in 0..Timeout
    /\ expired \subseteq 1..MaxLogLen
    /\ latestCkptLen \in 0..MaxLogLen

Init ==
    /\ up = [n \in Node |-> TRUE]
    /\ link = [p \in Node \X Node |-> TRUE]
    /\ leader = NoNode
    /\ chosen = << >>
    /\ log = [n \in Node |-> << >>]
    /\ taking = [n \in Node |-> FALSE]
    /\ ckpt = [n \in Node |-> 0]
    /\ pendingReport = [n \in Node |-> 0]
    /\ timer = 0
    /\ expired = {}
    /\ latestCkptLen = 0

-----------------------------------------------------------------------------
\* Environment actions

NodeFail(n) ==
    /\ up[n]
    /\ up' = [up EXCEPT ![n] = FALSE]
    /\ taking' = [taking EXCEPT ![n] = FALSE]
    /\ pendingReport' = [pendingReport EXCEPT ![n] = 0]
    /\ leader' = IF leader = n THEN NoNode ELSE leader
    /\ UNCHANGED <<link, chosen, log, ckpt, timer, expired, latestCkptLen>>

\* Recovery: restore from latest checkpoint combined with local persisted log
NodeRecover(n) ==
    /\ ~up[n]
    /\ up' = [up EXCEPT ![n] = TRUE]
    /\ log' = [log EXCEPT ![n] =
                 IF latestCkptLen > Len(log[n])
                 THEN SubSeq(chosen, 1, latestCkptLen)
                 ELSE log[n]]
    /\ UNCHANGED <<link, leader, chosen, taking, ckpt, pendingReport,
                   timer, expired, latestCkptLen>>

LinkFail(n, m) ==
    /\ n # m
    /\ link[<<n, m>>]
    /\ link' = [link EXCEPT ![<<n, m>>] = FALSE]
    /\ UNCHANGED <<up, leader, chosen, log, taking, ckpt, pendingReport,
                   timer, expired, latestCkptLen>>

LinkRecover(n, m) ==
    /\ n # m
    /\ ~link[<<n, m>>]
    /\ link' = [link EXCEPT ![<<n, m>>] = TRUE]
    /\ UNCHANGED <<up, leader, chosen, log, taking, ckpt, pendingReport,
                   timer, expired, latestCkptLen>>

-----------------------------------------------------------------------------
\* Consensus / leadership actions

BecomeLeader(n) ==
    /\ leader = NoNode
    /\ up[n]
    /\ HasQuorum(n)
    /\ log[n] = chosen
    /\ leader' = n
    /\ taking' = [taking EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<up, link, chosen, log, ckpt, pendingReport,
                   timer, expired, latestCkptLen>>

LeaderStepDown ==
    /\ leader # NoNode
    /\ ~HasQuorum(leader)
    /\ leader' = NoNode
    /\ UNCHANGED <<up, link, chosen, log, taking, ckpt, pendingReport,
                   timer, expired, latestCkptLen>>

\* Node n learns the next log entry from node m
Learn(n, m) ==
    /\ n # m
    /\ up[n] /\ up[m]
    /\ link[<<m, n>>]
    /\ Len(log[m]) > Len(log[n])
    /\ log' = [log EXCEPT ![n] = Append(log[n], log[m][Len(log[n]) + 1])]
    /\ UNCHANGED <<up, link, leader, chosen, taking, ckpt, pendingReport,
                   timer, expired, latestCkptLen>>

\* Leader grants a checkpoint lease to follower m via a replicated request
GrantLease(m) ==
    /\ leader # NoNode
    /\ up[leader]
    /\ HasQuorum(leader)
    /\ m # leader
    /\ m \in Reachable(leader)
    /\ Len(chosen) < MaxLogLen
    /\ LeaseReplaceable(chosen)
    /\ LET e == [type |-> "lease", node |-> m, pos |-> Len(chosen) + 1]
       IN /\ chosen' = Append(chosen, e)
          /\ log' = [log EXCEPT ![leader] = Append(chosen, e)]
    /\ timer' = 0
    /\ UNCHANGED <<up, link, leader, taking, ckpt, pendingReport,
                   expired, latestCkptLen>>

-----------------------------------------------------------------------------
\* Checkpoint actions

StartCheckpoint(n) ==
    /\ CanCheckpoint(n)
    /\ ~taking[n]
    /\ taking' = [taking EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<up, link, leader, chosen, log, ckpt, pendingReport,
                   timer, expired, latestCkptLen>>

CompleteCheckpoint(n) ==
    /\ taking[n]
    /\ CanCheckpoint(n)
    /\ taking' = [taking EXCEPT ![n] = FALSE]
    /\ ckpt' = [ckpt EXCEPT ![n] = HeldLeasePos(n)]
    /\ pendingReport' = [pendingReport EXCEPT ![n] = HeldLeasePos(n)]
    /\ latestCkptLen' = Max(latestCkptLen, Len(log[n]))
    /\ UNCHANGED <<up, link, leader, chosen, log, timer, expired>>

\* The node reports completion to the leader, which replicates a "done" entry
ReportDone(n) ==
    /\ pendingReport[n] > 0
    /\ up[n]
    /\ leader # NoNode
    /\ up[leader]
    /\ HasQuorum(leader)
    /\ link[<<n, leader>>]
    /\ pendingReport[n] = LastLeasePos(chosen)
    /\ ~DoneRecorded(chosen)
    /\ Len(chosen) < MaxLogLen
    /\ LET e == [type |-> "done", node |-> n, pos |-> pendingReport[n]]
       IN /\ chosen' = Append(chosen, e)
          /\ log' = [log EXCEPT ![leader] = Append(chosen, e)]
    /\ pendingReport' = [pendingReport EXCEPT ![n] = 0]
    /\ UNCHANGED <<up, link, leader, taking, ckpt, timer, expired, latestCkptLen>>

DropStaleReport(n) ==
    /\ pendingReport[n] > 0
    /\ \/ pendingReport[n] # LastLeasePos(chosen)
       \/ DoneRecorded(chosen)
    /\ pendingReport' = [pendingReport EXCEPT ![n] = 0]
    /\ UNCHANGED <<up, link, leader, chosen, log, taking, ckpt,
                   timer, expired, latestCkptLen>>

\* Logical time advances; the latest lease may expire
Tick ==
    /\ LastLeasePos(chosen) > 0
    /\ LastLeasePos(chosen) \notin expired
    /\ ~DoneRecorded(chosen)
    /\ timer < Timeout
    /\ timer' = timer + 1
    /\ IF timer + 1 = Timeout
       THEN /\ expired' = expired \cup {LastLeasePos(chosen)}
            /\ taking' = [n \in Node |->
                            taking[n] /\ HeldLeasePos(n) # LastLeasePos(chosen)]
       ELSE UNCHANGED <<expired, taking>>
    /\ UNCHANGED <<up, link, leader, chosen, log, ckpt, pendingReport,
                   latestCkptLen>>

-----------------------------------------------------------------------------
Next ==
    \/ \E n \in Node : NodeFail(n) \/ NodeRecover(n)
    \/ \E n, m \in Node : LinkFail(n, m) \/ LinkRecover(n, m)
    \/ \E n \in Node : BecomeLeader(n)
    \/ LeaderStepDown
    \/ \E n, m \in Node : Learn(n, m)
    \/ \E m \in Node : GrantLease(m)
    \/ \E n \in Node : StartCheckpoint(n)
    \/ \E n \in Node : CompleteCheckpoint(n)
    \/ \E n \in Node : ReportDone(n)
    \/ \E n \in Node : DropStaleReport(n)
    \/ Tick

Fairness ==
    /\ \A n \in Node : WF_vars(NodeRecover(n))
    /\ \A n, m \in Node : WF_vars(LinkRecover(n, m))
    /\ WF_vars(\E n \in Node : BecomeLeader(n))
    /\ WF_vars(LeaderStepDown)
    /\ \A n, m \in Node : WF_vars(Learn(n, m))
    /\ WF_vars(\E m \in Node : GrantLease(m))
    /\ \A n \in Node : WF_vars(StartCheckpoint(n))
    /\ \A n \in Node : WF_vars(CompleteCheckpoint(n))
    /\ \A n \in Node : WF_vars(ReportDone(n))
    /\ \A n \in Node : WF_vars(DropStaleReport(n))
    /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

MutualExclusionAuthorized ==
    \A n, m \in Node : (CanCheckpoint(n) /\ CanCheckpoint(m)) => n = m

MutualExclusionTaking ==
    \A n, m \in Node : (taking[n] /\ taking[m]) => n = m

LeaderNeverCheckpoints ==
    leader # NoNode => (~taking[leader] /\ ~CanCheckpoint(leader))

LeaseConsistency ==
    leader # NoNode =>
        /\ (~LeaderHasLease => \A n \in Node : ~CanCheckpoint(n))
        /\ (LeaderHasLease =>
              \A n \in Node : CanCheckpoint(n) => n = LeaseHolder(log[leader]))

ValidAuthorization ==
    \A n \in Node : taking[n] =>
        /\ CanCheckpoint(n)
        /\ LeaseHolder(log[n]) = n
        /\ HeldLeasePos(n) \notin expired

LogConsistency ==
    /\ \A n, m \in Node :
         \A i \in 1..Min(Len(log[n]), Len(log[m])) : log[n][i] = log[m][i]
    /\ \A n \in Node :
         /\ Len(log[n]) <= Len(chosen)
         /\ log[n] = SubSeq(chosen, 1, Len(log[n]))

LeaderUpToDate ==
    leader # NoNode => log[leader] = chosen

SafetyInvariant ==
    /\ TypeOK
    /\ MutualExclusionAuthorized
    /\ MutualExclusionTaking
    /\ LeaderNeverCheckpoints
    /\ LeaseConsistency
    /\ ValidAuthorization
    /\ LogConsistency
    /\ LeaderUpToDate

-----------------------------------------------------------------------------
\* Liveness properties

EventuallyCanCheckpoint ==
    <>(\E n \in Node : CanCheckpoint(n))

CheckpointInitiation ==
    \A n \in Node :
        CanCheckpoint(n) ~> (taking[n] \/ ~up[n] \/ HeldLeaseExpired(n))

CheckpointCompletion ==
    \A n \in Node :
        taking[n] ~> (~up[n] \/ HeldLeaseExpired(n)
                      \/ (HeldLeasePos(n) > 0 /\ ckpt[n] >= HeldLeasePos(n)))

EventuallyCheckpointCompleted ==
    <>(\E n \in Node : ckpt[n] > 0)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => (EventuallyCanCheckpoint /\ CheckpointInitiation
                 /\ CheckpointCompletion /\ EventuallyCheckpointCompleted)
=============================================================================
---------------------------- MODULE BFSCounterexampleSearch ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    States,          \* finite set of graph states
    InitStates,      \* initial states
    Violations,      \* target (violation) states
    Succ,            \* transition relation: Succ[s] = set of successors of s
    Constraint(_,_), \* pruning predicate Constraint(state, bfsLevel)
    K,               \* parallelism / dequeue window
    KnownCEs         \* (possibly empty) set of known counterexample sequences

ASSUME /\ IsFiniteSet(States)
       /\ InitStates \subseteq States
       /\ Violations \subseteq States
       /\ Succ \in [States -> SUBSET States]
       /\ K \in Nat \ {0}
       /\ KnownCEs \subseteq Seq(States)

VARIABLES
    queue,        \* sequence of discovered but unexplored states
    seen,         \* states discovered (recorded)
    explored,     \* states already expanded
    pred,         \* predecessor function on seen (roots map to themselves)
    level,        \* BFS level function on seen
    initPending,  \* initial states not yet examined
    status,       \* "init" | "explore" | "cex" | "done"
    result        \* reported counterexample path (<<>> if none)

vars == <<queue, seen, explored, pred, level, initPending, status, result>>

-----------------------------------------------------------------------------------------
(* Helper definitions *)

EmptyFn == [x \in {} |-> x]

Deadlock(s) == Succ[s] \subseteq {s}

IsTarget(s) == s \in Violations \/ Deadlock(s)

MaxLevel == Cardinality(States)

Min(a, b) == IF a < b THEN a ELSE b

Window == Min(K, Len(queue))

RemoveAt(q, i) == SubSeq(q, 1, i - 1) \o SubSeq(q, i + 1, Len(q))

\* All orderings in which a set of newly discovered states may be enqueued
Perms(S) == { f \in [1..Cardinality(S) -> S] :
                 \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j] }

\* Reconstruct a path from a root (initial state) to s via predecessor info
RECURSIVE PathTo(_)
PathTo(s) == IF pred[s] = s THEN <<s>> ELSE Append(PathTo(pred[s]), s)

-----------------------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ queue = <<>>
    /\ seen = {}
    /\ explored = {}
    /\ pred = EmptyFn
    /\ level = EmptyFn
    /\ initPending = InitStates
    /\ status = "init"
    /\ result = <<>>

-----------------------------------------------------------------------------------------
(* Actions *)

\* Examine initial states in any order
ProcessInit ==
    /\ status = "init"
    /\ \E s \in initPending :
         /\ initPending' = initPending \ {s}
         /\ IF ~Constraint(s, 0)
              THEN UNCHANGED <<queue, seen, pred, level, status, result>>
            ELSE IF IsTarget(s)
              THEN /\ status' = "cex"
                   /\ result' = <<s>>
                   /\ UNCHANGED <<queue, seen, pred, level>>
            ELSE /\ queue' = Append(queue, s)
                 /\ seen' = seen \cup {s}
                 /\ pred' = (s :> s) @@ pred
                 /\ level' = (s :> 0) @@ level
                 /\ UNCHANGED <<status, result>>
    /\ UNCHANGED explored

FinishInit ==
    /\ status = "init"
    /\ initPending = {}
    /\ status' = "explore"
    /\ UNCHANGED <<queue, seen, explored, pred, level, initPending, result>>

\* Dequeue one of the first min(K, Len(queue)) states and expand it
Expand ==
    /\ status = "explore"
    /\ queue # <<>>
    /\ \E i \in 1..Window :
         LET s   == queue[i]
             lvl == level[s] + 1
             new == { t \in Succ[s] : t \notin seen /\ Constraint(t, lvl) }
             bad == { t \in new : IsTarget(t) }
         IN /\ explored' = explored \cup {s}
            /\ IF bad # {}
                 THEN \E t \in bad :
                        /\ status' = "cex"
                        /\ result' = Append(PathTo(s), t)
                        /\ queue' = RemoveAt(queue, i)
                        /\ UNCHANGED <<seen, pred, level>>
                 ELSE \E p \in Perms(new) :
                        /\ queue' = RemoveAt(queue, i) \o p
                        /\ seen' = seen \cup new
                        /\ pred' = [t \in new |-> s] @@ pred
                        /\ level' = [t \in new |-> lvl] @@ level
                        /\ UNCHANGED <<status, result>>
    /\ UNCHANGED initPending

Finish ==
    /\ status = "explore"
    /\ queue = <<>>
    /\ status' = "done"
    /\ UNCHANGED <<queue, seen, explored, pred, level, initPending, result>>

Terminated ==
    /\ status \in {"cex", "done"}
    /\ UNCHANGED vars

Next == ProcessInit \/ FinishInit \/ Expand \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(ProcessInit \/ FinishInit \/ Expand \/ Finish)

-----------------------------------------------------------------------------------------
(* Graph-level definitions used by the properties *)

IsPath(p) == /\ Len(p) >= 1
             /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]

ValidCE(p) == /\ IsPath(p)
              /\ p[1] \in InitStates
              /\ IsTarget(p[Len(p)])

RECURSIVE ReachWithin(_)
ReachWithin(n) ==
    IF n = 0 THEN InitStates
    ELSE LET R == ReachWithin(n - 1) IN R \cup UNION { Succ[s] : s \in R }

Reachable == ReachWithin(MaxLevel)

ReachableTarget == \E s \in Reachable : IsTarget(s)

\* Shortest distance (in transitions) to a target; meaningful only if ReachableTarget
MinDist ==
    CHOOSE n \in 0..MaxLevel :
        /\ \E s \in ReachWithin(n) : IsTarget(s)
        /\ \A m \in 0..(n - 1) : ~(\E s \in ReachWithin(m) : IsTarget(s))

ExactLayer(n) == ReachWithin(n) \ (IF n = 0 THEN {} ELSE ReachWithin(n - 1))

\* Pruning never removes a state at its shortest-path distance
NoPruneOnShortest ==
    \A n \in 0..MaxLevel : \A s \in ExactLayer(n) : Constraint(s, n)

\* States that satisfy the pruning predicate at every possible level
Kept(s) == \A n \in 0..MaxLevel : Constraint(s, n)

RECURSIVE KeptWithin(_)
KeptWithin(n) ==
    IF n = 0 THEN { s \in InitStates : Kept(s) }
    ELSE LET R == KeptWithin(n - 1)
         IN R \cup { t \in UNION { Succ[s] : s \in R } : Kept(t) }

KeptReachableTarget == \E s \in KeptWithin(MaxLevel) : IsTarget(s)

ShortestCEs == { p \in [1..(MinDist + 1) -> States] : ValidCE(p) }

-----------------------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ queue \in Seq(States)
    /\ seen \subseteq States
    /\ explored \subseteq seen
    /\ DOMAIN pred = seen
    /\ \A s \in seen : pred[s] \in States
    /\ DOMAIN level = seen
    /\ \A s \in seen : level[s] \in 0..MaxLevel
    /\ initPending \subseteq InitStates
    /\ status \in {"init", "explore", "cex", "done"}
    /\ result \in Seq(States)

\* Safety: any reported counterexample is a valid path to a violation or deadlock
CounterexampleValid == status = "cex" => ValidCE(result)

\* Recorded predecessor information always yields valid paths from initial states
PredecessorPathsValid ==
    \A s \in seen : LET p == PathTo(s) IN IsPath(p) /\ p[1] \in InitStates

\* Termination with "done" only when the queue is empty
DoneMeansEmptyQueue == status = "done" => queue = <<>> /\ initPending = {}

\* BFS minimality for K = 1 when pruning does not cut shortest paths
BFSMinimality ==
    (K = 1 /\ status = "cex" /\ NoPruneOnShortest) => Len(result) = MinDist + 1

-----------------------------------------------------------------------------------------
(* Liveness properties (checked under FairSpec) *)

\* Completeness modulo pruning
Completeness == KeptReachableTarget => <>(status = "cex")

\* The exploration always terminates
Termination == <>(status \in {"cex", "done"})

\* With no reachable violation, exploration terminates with an empty queue
TerminationEmptyQueue ==
    ~ReachableTarget => <>(status = "done" /\ queue = <<>>)

\* Stabilization on a counterexample when known counterexamples are supplied
KnownCEsStabilize ==
    (KnownCEs # {} /\ KeptReachableTarget) => <>[](status = "cex")

\* With K = 1, the stabilized counterexample is one of the known ones and is
\* minimal among them (assuming KnownCEs are valid and include all shortest ones)
KnownCEsMinimal ==
    (/\ K = 1
     /\ KnownCEs # {}
     /\ ReachableTarget
     /\ NoPruneOnShortest
     /\ \A p \in KnownCEs : ValidCE(p)
     /\ ShortestCEs \subseteq KnownCEs)
    => <>[](/\ status = "cex"
            /\ result \in KnownCEs
            /\ \A p \in KnownCEs : Len(result) <= Len(p))

=========================================================================================
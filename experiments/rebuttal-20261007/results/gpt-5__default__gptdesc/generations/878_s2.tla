----------------------------- MODULE RootedSpanningTree -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    Nodes,            \* finite, nonempty set of nodes
    Edge,             \* undirected edge relation: subset of Nodes \X Nodes
    Root,             \* distinguished root in Nodes
    MaxCardinality    \* a natural number serving as finite "infinity"

ASSUME
    /\ Root \in Nodes
    /\ Nodes \subseteq Nat            \* not required, but convenient
    /\ MaxCardinality \in Nat
    /\ Edge \subseteq Nodes \X Nodes
    /\ \A v \in Nodes : ~ (<<v,v>> \in Edge)                       \* irreflexive
    /\ \A u,v \in Nodes : (<<u,v>> \in Edge) <=> (<<v,u>> \in Edge) \* symmetric
    /\ Nodes # {}                                                       \* nonempty

Adj(v) == { u \in Nodes : <<v,u>> \in Edge }

DistDomain == 0..MaxCardinality

VARIABLES mom, dist, done

vars == << mom, dist, done >>

Init ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> DistDomain]
    /\ \A v \in Nodes : mom[v] = v
    /\ dist[Root] = 0
    /\ \A v \in Nodes \ {Root} : dist[v] = MaxCardinality
    /\ done = FALSE

NoDecrease ==
    \A v \in Nodes : \A u \in Adj(v) : dist[u] >= dist[v]

Decrease(v, u, nd) ==
    /\ ~done
    /\ v \in Nodes
    /\ u \in Adj(v)
    /\ nd \in DistDomain
    /\ dist[u] < dist[v]
    /\ dist[u] \le nd
    /\ nd < dist[v]
    /\ mom' = [mom EXCEPT ![v] = u]
    /\ dist' = [dist EXCEPT ![v] = nd]
    /\ UNCHANGED << done >>

AnyDecrease ==
    \E v \in Nodes : \E u \in Adj(v) : \E nd \in DistDomain : Decrease(v, u, nd)

Terminate ==
    /\ ~done
    /\ NoDecrease
    /\ done' = TRUE
    /\ UNCHANGED << mom, dist >>

Next == AnyDecrease \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Postcondition characterizing a correct rooted spanning tree guided by dist as levels.
Post ==
    /\ mom[Root] = Root
    /\ \A v \in Nodes \ {Root} : mom[v] \in Adj(v)
    /\ dist[Root] = 0
    /\ \A v \in Nodes \ {Root} : dist[v] = dist[mom[v]] + 1
    /\ \A v \in Nodes : dist[v] \in DistDomain

\* Safety: termination implies the postcondition.
SafetyTerminationImpliesPost == [] (done => Post)

\* Liveness: eventual termination.
EventuallyTerminates == <> done

\* Additional temporal property: every node eventually has the root as its parent.
EveryNodeEventuallyHasRootParent == \A v \in Nodes : <> (mom[v] = Root)

THEOREM Spec => SafetyTerminationImpliesPost
THEOREM Spec => EventuallyTerminates
THEOREM Spec => EveryNodeEventuallyHasRootParent

====================================================================================
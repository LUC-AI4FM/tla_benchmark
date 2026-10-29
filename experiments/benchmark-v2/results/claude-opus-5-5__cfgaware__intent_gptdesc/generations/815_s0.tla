---------------------------- MODULE ParReach ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,  \* the fixed finite set of network nodes
          Root,   \* a distinguished node used for refinement
          Procs,  \* identifiers of the worker processes executing rounds
          Succ    \* the static network: Succ[n] = nodes n may forward to

ASSUME /\ Root \in Nodes
       /\ Procs # {}
       /\ Succ \in [Nodes -> SUBSET Nodes]

VARIABLES knows,  \* knows[n] = set of node identifiers known by n
          out     \* out[n]   = neighbors n forwarded to in the last round

vars == <<knows, out>>

-----------------------------------------------------------------------------
(* Helpers. Sequences are defined locally so that TLC can override Seq.    *)

Fanout == 2   \* bound on the number of distinct neighbors per round

Min(a, b) == IF a < b THEN a ELSE b

LimitedSeq(S) == UNION { [1..k -> S] : k \in 0..Cardinality(Nodes) }

Seq(S) == LimitedSeq(S)

Len(s) == Cardinality(DOMAIN s)

\* Each node has a fixed number of neighbors other than itself,
\* so it is connected to some nodes but not to all of them.
ConnectedToSomeButNotAll ==
  CHOOSE f \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes :
      /\ n \notin f[n]
      /\ Cardinality(f[n]) = Min(2, Cardinality(Nodes) - 1)

\* There is a path from n to m along Succ edges (length 0 allowed).
Reach(n, m) ==
  \E p \in Seq(Nodes) :
    /\ Len(p) >= 1
    /\ p[1] = n
    /\ p[Len(p)] = m
    /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]

\* Information flows along edges, so m can learn n iff n reaches m.
Reachers(m) == { n \in Nodes : Reach(n, m) }

SCC(m) == { n \in Nodes : Reach(n, m) /\ Reach(m, n) }

StronglyConnected == \A n, m \in Nodes : Reach(n, m)

\* Admissible neighbor selections that respect the forwarding bound.
OutChoices ==
  { o \in [Nodes -> SUBSET Nodes] :
      \A n \in Nodes : /\ o[n] \subseteq Succ[n]
                       /\ Cardinality(o[n]) <= Fanout }

-----------------------------------------------------------------------------
(* The protocol.                                                           *)

Init ==
  /\ knows = [n \in Nodes |-> {n}]
  /\ out \in OutChoices          \* nondeterministic initial neighbor choice

\* A synchronous round: every node chooses at most Fanout neighbors and a
\* subset of what it knows; every node unions in all incoming information.
Round ==
  \E o \in OutChoices, send \in [Nodes -> SUBSET Nodes] :
    /\ \A n \in Nodes : send[n] \subseteq knows[n]
    /\ out' = o
    /\ knows' = [m \in Nodes |->
                   knows[m] \cup UNION { send[n] : n \in {x \in Nodes : m \in o[x]} }]

\* A particular productive round: n forwards everything it knows to m only.
\* It is a special case of Round and is the target of the fairness condition.
EdgeRound(n, m) ==
  /\ m \in Succ[n]
  /\ ~(knows[n] \subseteq knows[m])
  /\ out' = [x \in Nodes |-> IF x = n THEN {m} ELSE {}]
  /\ knows' = [knows EXCEPT ![m] = @ \cup knows[n]]

Next == Round

Fairness == \A n \in Nodes : \A m \in Succ[n] : WF_vars(EdgeRound(n, m))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety.                                                                 *)

TypeOK ==
  /\ knows \in [Nodes -> SUBSET Nodes]
  /\ out \in [Nodes -> SUBSET Nodes]

\* Bounded forwarding: never more than Fanout distinct neighbors, all real.
BoundedForwarding ==
  \A n \in Nodes : /\ out[n] \subseteq Succ[n]
                   /\ Cardinality(out[n]) <= Fanout

\* No node ever learns a non-node identifier; knowledge is sound.
OnlyNodesKnown == \A n \in Nodes : knows[n] \subseteq Nodes

SelfKnown == \A n \in Nodes : n \in knows[n]

Sound == \A m \in Nodes : knows[m] \subseteq Reachers(m)

Inv == /\ TypeOK
       /\ BoundedForwarding
       /\ OnlyNodesKnown
       /\ SelfKnown
       /\ Sound

\* Knowledge monotonicity: a node's known set never shrinks.
Monotonic == [][\A n \in Nodes : knows[n] \subseteq knows'[n]]_vars

-----------------------------------------------------------------------------
(* Liveness and termination.                                               *)

Quiescent == \A n \in Nodes : \A m \in Succ[n] : knows[n] \subseteq knows[m]

\* Once quiescent, no further round alters any known set.
QuiescenceStable == [](Quiescent => [][UNCHANGED knows]_vars)

Termination == <>[]Quiescent

SCCLearned == <>[](\A m \in Nodes : SCC(m) \subseteq knows[m])

AllReachersLearned == <>[](\A m \in Nodes : knows[m] = Reachers(m))

GlobalReachability ==
  StronglyConnected => <>[](\A n \in Nodes : knows[n] = Nodes)

\* Refinement of the abstract reachability spec, observed at Root:
\* Root's knowledge starts at {Root}, grows monotonically within the set of
\* nodes that reach Root, and eventually equals that set.
Refines ==
  /\ knows[Root] = {Root}
  /\ [][ /\ knows[Root] \subseteq knows'[Root]
         /\ knows'[Root] \subseteq Reachers(Root) ]_(knows[Root])
  /\ <>[](knows[Root] = Reachers(Root))

THEOREM Spec => []Inv
THEOREM Spec => Monotonic /\ QuiescenceStable
THEOREM Spec => Termination /\ SCCLearned /\ GlobalReachability /\ Refines
=============================================================================
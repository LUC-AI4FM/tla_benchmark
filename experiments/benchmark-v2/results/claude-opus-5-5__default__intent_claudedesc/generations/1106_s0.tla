------------------------- MODULE SpanningTreeEcho -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,     \* set of processes
          root,     \* designated root process
          Nbrs,     \* Nbrs[p] = set of neighbors of p
          NoPrnt    \* special "no parent" value for the root

NotAProc == CHOOSE v : v \notin Proc \cup {NoPrnt}

RECURSIVE ReachN(_)
ReachN(n) == IF n = 0 THEN {root}
             ELSE ReachN(n-1) \cup UNION {Nbrs[q] : q \in ReachN(n-1)}

ASSUME /\ root \in Proc
       /\ NoPrnt \notin Proc
       /\ IsFiniteSet(Proc)
       /\ Nbrs \in [Proc -> SUBSET Proc]
       /\ \A p \in Proc : p \notin Nbrs[p]
       /\ \A p, q \in Proc : q \in Nbrs[p] <=> p \in Nbrs[q]   \* symmetric
       /\ ReachN(Cardinality(Proc)) = Proc                     \* connected

VARIABLES parent,    \* parent[p]: NoPrnt (root), NotAProc (not yet), or a neighbor
          rcvd,      \* rcvd[p]: neighbors from which p has received a message
          reported,  \* reported[p]: p has sent its report (echo) to its parent
          msgs       \* set of messages in transit

vars == <<parent, rcvd, reported, msgs>>

Msg == [type : {"M", "R"}, from : Proc, to : Proc]

TypeOK ==
  /\ parent \in [Proc -> Proc \cup {NoPrnt, NotAProc}]
  /\ rcvd \in [Proc -> SUBSET Proc]
  /\ reported \in [Proc -> BOOLEAN]
  /\ msgs \subseteq Msg

-----------------------------------------------------------------------------
Init ==
  /\ parent = [p \in Proc |-> IF p = root THEN NoPrnt ELSE NotAProc]
  /\ rcvd = [p \in Proc |-> {}]
  /\ reported = [p \in Proc |-> FALSE]
  /\ msgs = {[type |-> "M", from |-> root, to |-> q] : q \in Nbrs[root]}

\* Process p receives a message (exploration "M" or report "R").
\* On first reception, p adopts the sender as parent and forwards
\* exploration messages to all its other neighbors.
Receive(p) ==
  \E m \in msgs :
    /\ m.to = p
    /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m.from}]
    /\ IF parent[p] = NotAProc
         THEN /\ parent' = [parent EXCEPT ![p] = m.from]
              /\ msgs' = (msgs \ {m}) \cup
                   {[type |-> "M", from |-> p, to |-> q] : q \in Nbrs[p] \ {m.from}}
         ELSE /\ parent' = parent
              /\ msgs' = msgs \ {m}
    /\ UNCHANGED reported

\* A non-root process that has heard from all neighbors reports to its parent.
Report(p) ==
  /\ p # root
  /\ parent[p] \in Proc
  /\ rcvd[p] = Nbrs[p]
  /\ ~reported[p]
  /\ reported' = [reported EXCEPT ![p] = TRUE]
  /\ msgs' = msgs \cup {[type |-> "R", from |-> p, to |-> parent[p]]}
  /\ UNCHANGED <<parent, rcvd>>

Terminated == rcvd[root] = Nbrs[root]

Done == /\ Terminated
        /\ msgs = {}
        /\ UNCHANGED vars

Next == \/ \E p \in Proc : Receive(p) \/ Report(p)
        \/ Done

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Proc : WF_vars(Receive(p)) /\ WF_vars(Report(p))

-----------------------------------------------------------------------------
\* Following parent pointers n steps from p (stopping at root / unassigned)
RECURSIVE ParIter(_, _)
ParIter(p, n) ==
  IF n = 0 THEN p
  ELSE LET q == ParIter(p, n-1)
       IN IF q = root \/ parent[q] \notin Proc THEN q ELSE parent[q]

Joined(p) == parent[p] # NotAProc

\* Safety: parent pointers always form a tree rooted at root (no cycles)
TreeSafety ==
  /\ parent[root] = NoPrnt
  /\ \A p \in Proc \ {root} : parent[p] # NoPrnt
  /\ \A p \in Proc :
       parent[p] \in Proc =>
         /\ parent[p] \in Nbrs[p]
         /\ Joined(parent[p])
         /\ \E n \in 0..Cardinality(Proc) : ParIter(p, n) = root

\* When the root has terminated, the spanning tree covers all processes
TerminationCorrect ==
  Terminated => \A p \in Proc \ {root} : parent[p] \in Nbrs[p]

\* Final tree: every process reachable from the root is in the tree
SpanningTree ==
  /\ parent[root] = NoPrnt
  /\ \A p \in ReachN(Cardinality(Proc)) \ {root} :
        /\ parent[p] \in Nbrs[p]
        /\ \E n \in 0..Cardinality(Proc) : ParIter(p, n) = root

\* Liveness
AllJoin == <>(\A p \in Proc : Joined(p))
Termination == <>Terminated
EventuallySpanningTree == <>[]SpanningTree

THEOREM Spec => [](TypeOK /\ TreeSafety /\ TerminationCorrect)
THEOREM Spec => AllJoin /\ Termination /\ EventuallySpanningTree
=============================================================================
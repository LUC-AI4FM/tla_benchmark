---------------------------- MODULE MCSession10 ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Node, Edge, Root

ASSUME /\ Root \in Node
       /\ Edge \subseteq Node \X Node
       /\ IsFiniteSet(Node)

VARIABLES depth, parent, inbox

vars == <<depth, parent, inbox>>

Inf == Cardinality(Node)

Nbrs(n) == { m \in Node : m # n /\ (<<n, m>> \in Edge \/ <<m, n>> \in Edge) }

Msg == [from : Node, depth : 0 .. (Inf - 1)]

-----------------------------------------------------------------------------
(* Underlying system (Session10)                                          *)

Init ==
  /\ depth  = [n \in Node |-> IF n = Root THEN 0 ELSE Inf]
  /\ parent = [n \in Node |-> n]
  /\ inbox  = [n \in Node |-> IF n \in Nbrs(Root)
                                THEN << [from |-> Root, depth |-> 0] >>
                                ELSE << >>]

Receive(p) ==
  /\ inbox[p] # << >>
  /\ LET m == Head(inbox[p]) IN
       IF m.depth + 1 < depth[p]
         THEN /\ depth'  = [depth EXCEPT ![p] = m.depth + 1]
              /\ parent' = [parent EXCEPT ![p] = m.from]
              /\ inbox'  = [q \in Node |->
                              LET base == IF q = p THEN Tail(inbox[q])
                                                   ELSE inbox[q]
                              IN IF q \in Nbrs(p)
                                   THEN Append(base, [from |-> p,
                                                      depth |-> m.depth + 1])
                                   ELSE base]
         ELSE /\ inbox' = [inbox EXCEPT ![p] = Tail(inbox[p])]
              /\ UNCHANGED <<depth, parent>>

Terminated == \A n \in Node : inbox[n] = << >>

Done == Terminated /\ UNCHANGED vars

Next == (\E p \in Node : Receive(p)) \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(\E p \in Node : Receive(p))

-----------------------------------------------------------------------------
(* Model-checking wrapper: properties                                     *)

TypeOK ==
  /\ depth  \in [Node -> 0 .. Inf]
  /\ parent \in [Node -> Node]
  /\ inbox  \in [Node -> Seq(Msg)]
  /\ \A n \in Node : \A i \in 1 .. Len(inbox[n]) : inbox[n][i] \in Msg

Termination == <>Terminated

\* Nodes reachable from Root within k steps
RECURSIVE Reach(_)
Reach(k) == IF k = 0 THEN {Root}
            ELSE Reach(k - 1) \cup UNION { Nbrs(m) : m \in Reach(k - 1) }

\* Graph distance to Root (Inf if unreachable)
Distance(n) ==
  IF \E k \in 0 .. (Inf - 1) : n \in Reach(k)
    THEN CHOOSE k \in 0 .. (Inf - 1) :
           /\ n \in Reach(k)
           /\ \A j \in 0 .. (Inf - 1) : n \in Reach(j) => k <= j
    ELSE Inf

\* Length of the parent path from n to Root (Inf if no such path)
RECURSIVE PathLen(_, _)
PathLen(n, fuel) ==
  IF n = Root THEN 0
  ELSE IF fuel = 0 \/ parent[n] = n THEN Inf
  ELSE LET r == PathLen(parent[n], fuel - 1)
       IN IF r = Inf THEN Inf ELSE r + 1

ParentPathLength(n) == PathLen(n, Inf)

Postcondition ==
  \A n \in Node :
    /\ ParentPathLength(n) = Distance(n)
    /\ depth[n] = Distance(n)

Correctness == Terminated => Postcondition

CorrectnessProperty == [](Terminated => Postcondition)

THEOREM Spec => []TypeOK /\ Termination /\ []Correctness
=============================================================================
------------------------------ MODULE EchoTiny ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT initiator

VARIABLES pc, parent, rcvd, msgs

vars == <<pc, parent, rcvd, msgs>>

(***************************************************************************)
(* Ways of defining the set of nodes.                                      *)
(***************************************************************************)
NodesExplicit == {"a", "b", "c"}

NodesByDomain == DOMAIN [n \in {"a", "b", "c"} |-> TRUE]

Nodes == NodesExplicit

ASSUME NodesExplicit = NodesByDomain
ASSUME initiator \in Nodes

NoNode == "none"

(***************************************************************************)
(* Properties of relations, which are represented as Boolean-valued        *)
(* functions on Nodes \X Nodes.                                            *)
(***************************************************************************)
IsSymmetric(r)   == \A m, n \in Nodes : r[<<m, n>>] = r[<<n, m>>]
IsIrreflexive(r) == \A n \in Nodes : ~ r[<<n, n>>]

RECURSIVE ReachableFrom(_, _)
ReachableFrom(r, S) ==
  LET T == S \cup {y \in Nodes : \E x \in S : r[<<x, y>>]}
  IN  IF T = S THEN S ELSE ReachableFrom(r, T)

IsConnected(r) == \A n \in Nodes : ReachableFrom(r, {n}) = Nodes

(***************************************************************************)
(* Ways of defining the edge relation.                                     *)
(***************************************************************************)
\* 1. An explicit set of (directed) edges.
REdges == { <<"a", "b">>, <<"b", "a">>,
            <<"a", "c">>, <<"c", "a">>,
            <<"b", "c">>, <<"c", "b">> }

\* 2. A function defined by its domain.
RByDomain == [e \in Nodes \X Nodes |-> e \in REdges]

\* 3. A CHOOSE expression selecting a suitable relation.
RChoose == CHOOSE r \in [Nodes \X Nodes -> BOOLEAN] :
              /\ IsConnected(r)
              /\ IsSymmetric(r)
              /\ IsIrreflexive(r)

R == RByDomain

ASSUME IsConnected(R) /\ IsSymmetric(R) /\ IsIrreflexive(R)
ASSUME IsConnected(RChoose) /\ IsSymmetric(RChoose) /\ IsIrreflexive(RChoose)

Nbrs(n) == {m \in Nodes : R[<<n, m>>]}

(***************************************************************************)
(* The Echo algorithm.                                                     *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [Nodes -> {"start", "idle", "wait", "done"}]
  /\ parent \in [Nodes -> Nodes \cup {NoNode}]
  /\ rcvd \in [Nodes -> Nat]
  /\ msgs \subseteq (Nodes \X Nodes)

Init ==
  /\ pc = [n \in Nodes |-> IF n = initiator THEN "start" ELSE "idle"]
  /\ parent = [n \in Nodes |-> NoNode]
  /\ rcvd = [n \in Nodes |-> 0]
  /\ msgs = {}

Start ==
  /\ pc[initiator] = "start"
  /\ msgs' = msgs \cup {<<initiator, k>> : k \in Nbrs(initiator)}
  /\ pc' = [pc EXCEPT ![initiator] =
              IF Nbrs(initiator) = {} THEN "done" ELSE "wait"]
  /\ UNCHANGED <<parent, rcvd>>

Receive(n, m) ==
  /\ <<m, n>> \in msgs
  /\ pc[n] \in {"idle", "wait"}
  /\ LET first    == pc[n] = "idle"
         newRcvd  == rcvd[n] + 1
         par      == IF first THEN m ELSE parent[n]
         fwd      == IF first THEN {<<n, k>> : k \in Nbrs(n) \ {m}} ELSE {}
         finished == newRcvd = Cardinality(Nbrs(n))
         echo     == IF finished /\ n # initiator THEN {<<n, par>>} ELSE {}
     IN  /\ parent' = [parent EXCEPT ![n] = par]
         /\ rcvd' = [rcvd EXCEPT ![n] = newRcvd]
         /\ msgs' = (msgs \ {<<m, n>>}) \cup fwd \cup echo
         /\ pc' = [pc EXCEPT ![n] = IF finished THEN "done" ELSE "wait"]

Next == Start \/ \E n, m \in Nodes : Receive(n, m)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
ParentIsNeighbor ==
  \A n \in Nodes \ {initiator} :
     pc[n] # "idle" => (parent[n] \in Nodes /\ R[<<n, parent[n]>>])

TerminationCorrect ==
  pc[initiator] = "done" =>
     /\ \A n \in Nodes : pc[n] = "done"
     /\ msgs = {}

Terminates == <>(pc[initiator] = "done")

(***************************************************************************)
(* Test specification and TLC postcondition.                               *)
(***************************************************************************)
TestSpec == PrintT(RChoose) /\ Spec

PostCondition == TLCGet("stats").distinct >= 1

=============================================================================
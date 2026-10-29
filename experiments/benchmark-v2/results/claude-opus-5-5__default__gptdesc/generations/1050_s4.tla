------------------------------- MODULE MCEcho -------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(* Model-checking instance of the Echo protocol on a three-node graph.    *)
(***************************************************************************)

N1 == {1, 2, 3}

I1 == CHOOSE n \in N1 : TRUE

\* A graph given as a function over node pairs: the cycle 1-2-3-1.
R1 == [ edge \in N1 \X N1 |->
          CASE edge = <<1,2>> -> TRUE
            [] edge = <<2,1>> -> TRUE
            [] edge = <<2,3>> -> TRUE
            [] edge = <<3,2>> -> TRUE
            [] edge = <<1,3>> -> TRUE
            [] edge = <<3,1>> -> TRUE
            [] OTHER          -> FALSE ]

RECURSIVE ReachFrom(_, _, _)
ReachFrom(r, S, k) ==
  IF k = 0 THEN S
  ELSE ReachFrom(r, S \cup {n \in N1 : \E m \in S : r[m, n]}, k - 1)

IsConnected(r)   == \A m \in N1 : ReachFrom(r, {m}, Cardinality(N1)) = N1
IsSymmetric(r)   == \A m, n \in N1 : r[m, n] = r[n, m]
IsIrreflexive(r) == \A n \in N1 : ~ r[n, n]

\* A graph chosen to satisfy the assumptions of the Echo protocol.
R2 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :
         IsConnected(r) /\ IsSymmetric(r) /\ IsIrreflexive(r)

ASSUME IsConnected(R1) /\ IsSymmetric(R1) /\ IsIrreflexive(R1)
ASSUME IsConnected(R2) /\ IsSymmetric(R2) /\ IsIrreflexive(R2)

(***************************************************************************)
(* Protocol parameters bound to the concrete model values.                 *)
(***************************************************************************)
Node      == N1
initiator == I1
R         == R2

NoNode == CHOOSE x : x \notin Node

Neighbors(n) == {m \in Node : R[m, n]}

(***************************************************************************)
(* The Echo protocol.                                                      *)
(***************************************************************************)
VARIABLES inbox, pc, parent, rcvd

vars == <<inbox, pc, parent, rcvd>>

Msg == {"m"} \X Node

TypeOK ==
  /\ inbox  \in [Node -> SUBSET Msg]
  /\ pc     \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ rcvd   \in [Node -> 0..Cardinality(Node)]

Init ==
  /\ inbox  = [n \in Node |-> {}]
  /\ pc     = [n \in Node |-> "n0"]
  /\ parent = [n \in Node |-> NoNode]
  /\ rcvd   = [n \in Node |-> 0]

n0(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN inbox' = [m \in Node |->
                        IF m \in Neighbors(self)
                          THEN inbox[m] \cup {<<"m", self>>}
                          ELSE inbox[m]]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED <<parent, rcvd>>

n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(Neighbors(self))
       THEN \E msg \in inbox[self] :
              LET first == rcvd[self] = 0 /\ self # initiator
              IN  /\ inbox' = [m \in Node |->
                                 IF m = self
                                   THEN inbox[self] \ {msg}
                                 ELSE IF first /\ m \in Neighbors(self) \ {msg[2]}
                                   THEN inbox[m] \cup {<<"m", self>>}
                                 ELSE inbox[m]]
                  /\ parent' = IF first
                                 THEN [parent EXCEPT ![self] = msg[2]]
                                 ELSE parent
                  /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
                  /\ pc' = pc
       ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED <<inbox, parent, rcvd>>

n2(self) ==
  /\ pc[self] = "n2"
  /\ IF self # initiator
       THEN inbox' = [inbox EXCEPT ![parent[self]] = @ \cup {<<"m", self>>}]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED <<parent, rcvd>>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating == /\ \A n \in Node : pc[n] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
RECURSIVE Ancestor(_, _)
Ancestor(n, k) ==
  IF k = 0 \/ n = initiator \/ n = NoNode THEN n
  ELSE Ancestor(parent[n], k - 1)

SpanningTree ==
  \A n \in Node \ {initiator} :
     /\ parent[n] \in Neighbors(n)
     /\ Ancestor(n, Cardinality(Node)) = initiator

Correctness == (\A n \in Node : pc[n] = "Done") => SpanningTree

InitiatorNoParent == parent[initiator] = NoNode

Termination == <>(\A n \in Node : pc[n] = "Done")

(***************************************************************************)
(* TLC-specific test definitions.                                          *)
(***************************************************************************)
TestSpec == PrintT(R) /\ Spec

View == <<inbox, pc, parent, rcvd>>

PostCondition == TLCGet("stats").distinct >= 1

THEOREM Spec => [](TypeOK /\ Correctness /\ InitiatorNoParent)
THEOREM Spec => Termination
=============================================================================
---------------------------- MODULE MCChangRoberts ----------------------------
EXTENDS Naturals, Sequences

------------------------------ MODULE ChangRoberts ------------------------------
(***************************************************************************)
(* Chang-Roberts leader election on a unidirectional ring of N nodes.      *)
(* Each node has a unique identifier Id[n]. Initiators send their own id   *)
(* to their successor. A node that receives a smaller id than its own      *)
(* forwards it and loses. A node that receives a larger id discards it. A  *)
(* node that receives its own id back has won the election.                *)
(***************************************************************************)
CONSTANTS N, Id

ASSUME NAssump  == N \in Nat \ {0}
ASSUME IdAssump == /\ Id \in Seq(Nat)
                   /\ Len(Id) = N
                   /\ \A m, n \in 1 .. N : m # n => Id[m] # Id[n]

Node == 1 .. N

succ(n) == IF n = N THEN 1 ELSE n + 1

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

TypeOK ==
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ pc \in [Node -> {"n0", "n1"}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

Init ==
  /\ msgs = [n \in Node |-> {}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
  /\ pc = [self \in Node |-> "n0"]

n0(self) ==
  /\ pc[self] = "n0"
  /\ IF initiator[self]
       THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
       ELSE msgs' = msgs
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << initiator, state >>

n1(self) ==
  /\ pc[self] = "n1"
  /\ \E id \in msgs[self] :
       LET rest == [msgs EXCEPT ![self] = @ \ {id}]
       IN  IF state[self] = "lost"
             THEN /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                  /\ state' = state
             ELSE IF id < Id[self]
                    THEN /\ state' = [state EXCEPT ![self] = "lost"]
                         /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                    ELSE /\ msgs' = rest
                         /\ IF id = Id[self]
                              THEN state' = [state EXCEPT ![self] = "won"]
                              ELSE state' = state
  /\ pc' = pc
  /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

(***************************************************************************)
(* Safety: a node that won is an initiator, all other nodes have lost, and *)
(* the winner holds the smallest identifier among all initiators.          *)
(***************************************************************************)
Correctness ==
  \A n \in Node : state[n] = "won" =>
     /\ initiator[n]
     /\ \A m \in Node \ {n} :
          /\ state[m] = "lost"
          /\ initiator[m] => Id[m] > Id[n]

(***************************************************************************)
(* Liveness: if some node is an initiator, eventually some node wins.      *)
(***************************************************************************)
Liveness == (\E n \in Node : initiator[n]) ~> (\E n \in Node : state[n] = "won")
=================================================================================
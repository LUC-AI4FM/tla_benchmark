---------------------------- MODULE MC_ChangRoberts ----------------------------
(***************************************************************************)
(* Model-checking module for the Chang-Roberts leader election algorithm   *)
(* on a unidirectional ring of N processes. It fixes the identifier        *)
(* function Id to be the identity on 1 .. N. The algorithm is included     *)
(* here so that the module is self-contained.                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

Node == 1 .. N

\* Identifier function: process n has identifier n
Id == [n \in Node |-> n]

\* Successor of a node on the ring
succ(n) == IF n = N THEN 1 ELSE n + 1

-----------------------------------------------------------------------------
(* Initial states *)

Init ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ state = [n \in Node |-> IF initiator[n] THEN "cand" ELSE "lost"]
  /\ msgs = [n \in Node |-> {}]
  /\ pc = [self \in Node |-> "n0"]

-----------------------------------------------------------------------------
(* Actions *)

\* An initiator sends its own identifier to its successor
n0(self) ==
  /\ pc[self] = "n0"
  /\ IF initiator[self]
       THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
       ELSE UNCHANGED msgs
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << initiator, state >>

\* A node receives an identifier and reacts to it
n1(self) ==
  /\ pc[self] = "n1"
  /\ \E id \in msgs[self] :
       LET rest == [msgs EXCEPT ![self] = @ \ {id}]
       IN  IF state[self] = "lost"
             THEN /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                  /\ UNCHANGED state
             ELSE IF id < Id[self]
                    THEN /\ msgs' = rest          \* swallow smaller identifier
                         /\ UNCHANGED state
                    ELSE IF id = Id[self]
                           THEN /\ state' = [state EXCEPT ![self] = "won"]
                                /\ msgs' = rest
                           ELSE /\ state' = [state EXCEPT ![self] = "lost"]
                                /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ pc \in [Node -> {"n0", "n1"}]

\* At most one node is ever elected leader
Correctness ==
  \A m, n \in Node : state[m] = "won" /\ state[n] = "won" => m = n

\* The elected leader is the initiator with the largest identifier
LeaderIsMax ==
  \A n \in Node : state[n] = "won" =>
     /\ initiator[n]
     /\ \A m \in Node : initiator[m] => Id[m] <= Id[n]

\* If some node initiates, eventually a leader is elected
Liveness ==
  (\E n \in Node : initiator[n]) => <>(\E n \in Node : state[n] = "won")

THEOREM Spec => [](TypeOK /\ Correctness /\ LeaderIsMax)
THEOREM Spec => Liveness
=============================================================================
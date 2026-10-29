---------------------------- MODULE MCChangRoberts ----------------------------
(***************************************************************************)
(* Model-checking module for the Chang-Roberts leader election algorithm   *)
(* on a unidirectional ring of N nodes. In the original setup this wrapper *)
(* would contain                                                           *)
(*     INSTANCE ChangRoberts                                               *)
(* and would supply N and Id. Here the algorithm is written out inline so  *)
(* that the module parses on its own with no other files.                  *)
(* The identifier function Id maps each node index in 1..N to itself.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

Node == 1 .. N

\* The identifier function: each process index is mapped to itself.
Id == [n \in Node |-> n]

\* Successor of a node on the ring
succ(n) == IF n = N THEN 1 ELSE n + 1

TypeOK ==
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ pc \in [Node -> {"n0", "n1"}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

Init ==
  /\ msgs = [n \in Node |-> {}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state = [n \in Node |-> IF initiator[n] THEN "cand" ELSE "lost"]
  /\ pc = [n \in Node |-> "n0"]

\* Initiators send their own identifier to their successor.
n0(self) ==
  /\ pc[self] = "n0"
  /\ IF initiator[self]
       THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
       ELSE UNCHANGED msgs
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << initiator, state >>

\* A node receives a message and handles it.
n1(self) ==
  /\ pc[self] = "n1"
  /\ \E id \in msgs[self] :
       LET rmsgs == [msgs EXCEPT ![self] = @ \ {id}]
       IN  IF ~initiator[self] \/ id < Id[self]
             THEN \* forward the message and give up candidacy
                  /\ msgs' = [rmsgs EXCEPT ![succ(self)] = @ \cup {id}]
                  /\ state' = [state EXCEPT ![self] = "lost"]
             ELSE IF id = Id[self]
                    THEN \* own identifier came back: this node is elected
                         /\ msgs' = rmsgs
                         /\ state' = [state EXCEPT ![self] = "won"]
                    ELSE \* larger identifier: drop the message
                         /\ msgs' = rmsgs
                         /\ UNCHANGED state
  /\ pc' = pc
  /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
(* Properties *)

\* No two different nodes are ever both elected.
Correctness ==
  \A i, j \in Node : state[i] = "won" /\ state[j] = "won" => i = j

\* Any node that wins is the initiator with the smallest identifier.
WinnerIsMin ==
  \A i \in Node :
    state[i] = "won" =>
      /\ initiator[i]
      /\ \A j \in Node : initiator[j] => Id[i] <= Id[j]

\* If at least one node is an initiator, a leader is eventually elected.
Liveness ==
  (\E n \in Node : initiator[n]) ~> (\E n \in Node : state[n] = "won")

THEOREM Spec => [](TypeOK /\ Correctness /\ WinnerIsMin)
THEOREM Spec => Liveness
=============================================================================
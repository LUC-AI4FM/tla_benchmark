---------------------------- MODULE ChangRoberts ----------------------------
(***************************************************************************)
(* Chang-Roberts leader election on a unidirectional ring of N nodes.      *)
(* Each node has a unique natural-number identity given by the sequence    *)
(* Id. Any subset of nodes may initiate the algorithm. The initiator with  *)
(* the smallest identity is intended to be elected leader.                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N, Id

ASSUME NodeAssumption == N \in Nat \ {0}
ASSUME IdAssumption ==
         /\ Id \in Seq(Nat)
         /\ Len(Id) = N
         /\ \A m, n \in 1 .. N : m # n => Id[m] # Id[n]

Node == 1 .. N

succ(n) == IF n = N THEN 1 ELSE n + 1

(* --algorithm ChangRoberts {
  variables
    initiator \in [Node -> BOOLEAN],
    msgs = [n \in Node |-> {}];
  fair process (node \in Node)
    variable state = IF initiator[self] THEN "cand" ELSE "lost";
  {
   n0: if (initiator[self]) {
          msgs[succ(self)] := @ \union {Id[self]}
       };
   n1: while (TRUE) {
         with (id \in msgs[self],
               rest = [msgs EXCEPT ![self] = @ \ {id}]) {
           if (id = Id[self]) {
              \* own identity came back: won
              state := "won";
              msgs := rest
           } else if (state = "lost" \/ id < Id[self]) {
              \* pass on the message, and lose if still a candidate
              state := "lost";
              msgs := [rest EXCEPT ![succ(self)] = @ \union {id}]
           } else {
              \* candidate receives larger identity: swallow it
              msgs := rest
           }
         }
       }
  }
} *)
\* BEGIN TRANSLATION
VARIABLES initiator, msgs, pc, state

vars == << initiator, msgs, pc, state >>

ProcSet == Node

Init == /\ initiator \in [Node -> BOOLEAN]
        /\ msgs = [n \in Node |-> {}]
        /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF initiator[self]
                  THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \union {Id[self]}]
                  ELSE UNCHANGED msgs
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << initiator, state >>

n1(self) == /\ pc[self] = "n1"
            /\ \E id \in msgs[self] :
                 LET rest == [msgs EXCEPT ![self] = @ \ {id}] IN
                   IF id = Id[self]
                      THEN /\ state' = [state EXCEPT ![self] = "won"]
                           /\ msgs' = rest
                      ELSE IF state[self] = "lost" \/ id < Id[self]
                              THEN /\ state' = [state EXCEPT ![self] = "lost"]
                                   /\ msgs' = [rest EXCEPT ![succ(self)] = @ \union {id}]
                              ELSE /\ msgs' = rest
                                   /\ UNCHANGED state
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "n1" /\ msgs[self] = {}
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

\* END TRANSLATION

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ pc \in [Node -> {"n0", "n1"}]
  /\ state \in [Node -> {"cand", "lost", "won"}]

(* If some node has won, it is an initiator with the smallest identity    *)
(* among all initiators, and all other nodes have lost.                    *)
Correctness ==
  \A i \in Node : state[i] = "won" =>
     /\ initiator[i]
     /\ \A j \in Node \ {i} :
          /\ state[j] = "lost"
          /\ initiator[j] => Id[i] < Id[j]

(* If some candidate exists, eventually some node wins. *)
Liveness ==
  (\E i \in Node : state[i] = "cand") => <>(\E i \in Node : state[i] = "won")

=============================================================================
------------------------------ MODULE ChangRoberts ------------------------------
(***************************************************************************)
(* Algorithm by Chang and Roberts for electing a leader on a              *)
(* unidirectional ring. The algorithm originally appeared as              *)
(* E. Chang, R. Roberts: An improved algorithm for decentralized          *)
(* extrema-finding in circular configurations of processes,               *)
(* Communications of the ACM 22(5): 281-283, 1979.                        *)
(***************************************************************************)
EXTENDS Naturals, Sequences

(***************************************************************************)
(* Constant parameters:                                                    *)
(* - N is the number of nodes.                                             *)
(* - Id is a sequence of natural numbers of length N such that Id[i]      *)
(*   is the identity of node i.                                            *)
(* Any subset of nodes may initiate the algorithm. The node with the      *)
(* smallest identity is elected as the leader.                             *)
(***************************************************************************)
CONSTANTS N, Id

Node == 1 .. N

ASSUME
  /\ N \in Nat \ {0}
  /\ Id \in Seq(Nat)
  /\ Len(Id) = N
  /\ \A m, n \in Node : m # n => Id[m] # Id[n]   \* identities are unique

succ(n) == IF n = N THEN 1 ELSE n + 1   \* successor along the ring

(** Chang-Roberts algorithm written in PlusCal
--algorithm ChangRoberts {
  (* msgs[n]: messages waiting to be received by node n *)
  variable msgs = [n \in Node |-> {}];
  fair process (node \in Node)
     variables
       \* this node may or may not be an initiator
       initiator \in BOOLEAN,
       state = IF initiator THEN "cand" ELSE "lost"; {
   \* initiators send their own identity to their neighbor
   n0: if (initiator) {
          msgs[succ(self)] := @ \cup {Id[self]}
       };
   n1: while (TRUE) {
         \* handle some incoming message
         with (id \in msgs[self],
               nmsgs = [msgs EXCEPT ![self] = @ \ {id}]) {
            if (id = Id[self]) {
               \* found own identity: become leader
               state := "won";
               msgs := nmsgs;
            } else if (id < Id[self]) {
               \* pass on smaller identity
               if (state = "cand") { state := "lost" };
               msgs := [nmsgs EXCEPT ![succ(self)] = @ \cup {id}]
            } else {
               \* swallow larger identity
               msgs := nmsgs
            }
         }
       }
  }
}
**)
\* BEGIN TRANSLATION
VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

ProcSet == (Node)

Init == (* Global variables *)
        /\ msgs = [n \in Node |-> {}]
        (* Process node *)
        /\ initiator \in [Node -> BOOLEAN]
        /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF initiator[self]
                  THEN /\ msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
                  ELSE /\ TRUE
                       /\ msgs' = msgs
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << initiator, state >>

n1(self) == /\ pc[self] = "n1"
            /\ \E id \in msgs[self]:
                 LET nmsgs == [msgs EXCEPT ![self] = @ \ {id}] IN
                   IF id = Id[self]
                      THEN /\ state' = [state EXCEPT ![self] = "won"]
                           /\ msgs' = nmsgs
                      ELSE /\ IF id < Id[self]
                                 THEN /\ IF state[self] = "cand"
                                            THEN /\ state' = [state EXCEPT ![self] = "lost"]
                                            ELSE /\ TRUE
                                                 /\ state' = state
                                      /\ msgs' = [nmsgs EXCEPT ![succ(self)] = @ \cup {id}]
                                 ELSE /\ msgs' = nmsgs
                                      /\ state' = state
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node: node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [Node -> {"n0", "n1", "Done"}]
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

(***************************************************************************)
(* Safety property: if node n wins the election, then n is an initiator,  *)
(* all other nodes have lost, and every other initiator has a larger      *)
(* identity than n.                                                        *)
(***************************************************************************)
Correctness ==
  \A n \in Node : state[n] = "won" =>
     /\ initiator[n]
     /\ \A m \in Node \ {n} :
           /\ state[m] = "lost"
           /\ initiator[m] => Id[m] > Id[n]

(***************************************************************************)
(* Liveness property: if some candidate exists, eventually some node wins. *)
(***************************************************************************)
Liveness ==
  (\E n \in Node : state[n] = "cand") => <>(\E n \in Node : state[n] = "won")

THEOREM Spec => []TypeOK /\ []Correctness /\ Liveness
=============================================================================
------------------------------ MODULE ChangRoberts ------------------------------
(***************************************************************************)
(* Algorithm by Chang and Roberts for electing a leader on a               *)
(* unidirectional ring of N nodes. Each node has a unique natural-number   *)
(* identity given by the sequence Id. Any subset of nodes may initiate     *)
(* the algorithm. The node with the smallest identity among the initiators *)
(* is elected leader.                                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N, Id

ASSUME
  /\ N \in Nat \ {0}
  /\ Id \in Seq(Nat)
  /\ Len(Id) = N
  /\ \A m, n \in 1 .. N : m # n => Id[m] # Id[n]

Node == 1 .. N

succ(n) == IF n = N THEN 1 ELSE n + 1

(***************************************************************************
--algorithm ChangRoberts {
  variable msgs = [n \in Node |-> {}];
  fair process (node \in Node)
    variables initiator \in BOOLEAN,
              state = IF initiator THEN "cand" ELSE "lost"; {
   n0: if (initiator) {
         msgs[succ(self)] := @ \cup {Id[self]}
       };
   n1: while (TRUE) {
         with (id \in msgs[self],
               msgs_ = [msgs EXCEPT ![self] = @ \ {id}]) {
           if (state = "lost") {
              msgs := [msgs_ EXCEPT ![succ(self)] = @ \cup {id}]
           } else if (id < Id[self]) {
              state := "lost";
              msgs := [msgs_ EXCEPT ![succ(self)] = @ \cup {id}]
           } else {
              msgs := msgs_;
              if (id = Id[self]) { state := "won" }
           }
         }
       }
  }
}
 ***************************************************************************)
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
                  THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
                  ELSE msgs' = msgs
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << initiator, state >>

n1(self) == /\ pc[self] = "n1"
            /\ \E id \in msgs[self]:
                 LET msgs_ == [msgs EXCEPT ![self] = @ \ {id}] IN
                   IF state[self] = "lost"
                      THEN /\ msgs' = [msgs_ EXCEPT ![succ(self)] = @ \cup {id}]
                           /\ state' = state
                      ELSE IF id < Id[self]
                              THEN /\ state' = [state EXCEPT ![self] = "lost"]
                                   /\ msgs' = [msgs_ EXCEPT ![succ(self)] = @ \cup {id}]
                              ELSE /\ msgs' = msgs_
                                   /\ IF id = Id[self]
                                         THEN state' = [state EXCEPT ![self] = "won"]
                                         ELSE state' = state
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

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
(* Safety property: if node n wins the election, it is an initiator, and   *)
(* every other initiator has lost and has a larger identity than n.        *)
(***************************************************************************)
Correctness ==
  \A n \in Node : state[n] = "won" =>
     /\ initiator[n]
     /\ \A m \in Node \ {n} :
          /\ state[m] = "lost"
          /\ initiator[m] => Id[m] > Id[n]

(***************************************************************************)
(* Liveness property: if there is some candidate, eventually some node     *)
(* wins the election.                                                      *)
(***************************************************************************)
Liveness == (\E n \in Node : state[n] = "cand") => <>(\E n \in Node : state[n] = "won")

=============================================================================
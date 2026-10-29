---- MODULE ChangRoberts ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, Id

Node == 1 .. N

ASSUME NodeAssumption == N \in Nat \ {0}

ASSUME IdsUnique == \A m, n \in Node : m # n => Id[m] # Id[n]

succ(n) == IF n = N THEN 1 ELSE n + 1

min(S) == CHOOSE x \in S : \A y \in S : x <= y

(* --algorithm ChangRoberts {
  variables
    initiator \in [Node -> BOOLEAN],
    msgs = [n \in Node |-> {}];
  fair process (node \in Node)
    variables state = IF initiator[self] THEN "cand" ELSE "lost";
  {
   n0: if (initiator[self]) {
         msgs[succ(self)] := @ \union {Id[self]}
       };
   n1: while (TRUE) {
         with (id \in msgs[self], _msgs = [msgs EXCEPT ![self] = @ \ {id}]) {
           if (state = "lost") {
             msgs := [_msgs EXCEPT ![succ(self)] = @ \union {id}]
           } else if (id < Id[self]) {
             state := "lost";
             msgs := [_msgs EXCEPT ![succ(self)] = @ \union {id}]
           } else {
             msgs := _msgs;
             if (id = Id[self]) { state := "won" }
           }
         }
       }
  }
} *)

VARIABLES initiator, msgs, pc, state

vars == << initiator, msgs, pc, state >>

ProcSet == Node

Init ==
    /\ initiator \in [Node -> BOOLEAN]
    /\ msgs = [n \in Node |-> {}]
    /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
    /\ pc = [self \in ProcSet |-> "n0"]

n0(self) ==
    /\ pc[self] = "n0"
    /\ IF initiator[self]
         THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \union {Id[self]}]
         ELSE UNCHANGED msgs
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED << initiator, state >>

n1(self) ==
    /\ pc[self] = "n1"
    /\ \E id \in msgs[self] :
         LET _msgs == [msgs EXCEPT ![self] = @ \ {id}] IN
           IF state[self] = "lost"
             THEN /\ msgs' = [_msgs EXCEPT ![succ(self)] = @ \union {id}]
                  /\ UNCHANGED state
             ELSE IF id < Id[self]
                    THEN /\ state' = [state EXCEPT ![self] = "lost"]
                         /\ msgs' = [_msgs EXCEPT ![succ(self)] = @ \union {id}]
                    ELSE /\ msgs' = _msgs
                         /\ IF id = Id[self]
                              THEN state' = [state EXCEPT ![self] = "won"]
                              ELSE UNCHANGED state
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------

TypeOK ==
    /\ initiator \in [Node -> BOOLEAN]
    /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
    /\ pc \in [Node -> {"n0", "n1"}]
    /\ state \in [Node -> {"cand", "lost", "won"}]

Correctness ==
    \A n \in Node : state[n] = "won" =>
        /\ initiator[n]
        /\ \A m \in Node \ {n} : state[m] = "lost"
        /\ Id[n] = min({Id[m] : m \in {k \in Node : initiator[k]}})

Liveness ==
    (\E n \in Node : state[n] = "cand") ~> (\E n \in Node : state[n] = "won")

=============================================================================
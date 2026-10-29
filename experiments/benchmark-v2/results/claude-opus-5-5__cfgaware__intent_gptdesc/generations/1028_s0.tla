---------------------------- MODULE ChangRoberts ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS N, Id

ASSUME NAssump == N \in Nat \ {0}
ASSUME IdAssump == /\ Id \in Seq(Nat)
                   /\ Len(Id) = N
                   /\ \A m, n \in 1..N : m # n => Id[m] # Id[n]

Node == 1 .. N

succ(n) == IF n = N THEN 1 ELSE n + 1

IdSet == { Id[n] : n \in Node }

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

-----------------------------------------------------------------------------

Init == /\ msgs = [n \in Node |-> {}]
        /\ initiator \in [Node -> BOOLEAN]
        /\ state = [n \in Node |-> IF initiator[n] THEN "cand" ELSE "lost"]
        /\ pc = [n \in Node |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF initiator[self]
                  THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
                  ELSE UNCHANGED msgs
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << initiator, state >>

n1(self) == /\ pc[self] = "n1"
            /\ \E id \in msgs[self] :
                 LET rest == [msgs EXCEPT ![self] = @ \ {id}]
                 IN  IF state[self] = "lost"
                        THEN /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                             /\ UNCHANGED state
                        ELSE IF id < Id[self]
                                THEN /\ state' = [state EXCEPT ![self] = "lost"]
                                     /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                                ELSE /\ msgs' = rest
                                     /\ IF id = Id[self]
                                           THEN state' = [state EXCEPT ![self] = "won"]
                                           ELSE UNCHANGED state
            /\ pc' = pc
            /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Quiescent == /\ \A n \in Node : pc[n] = "n1" /\ msgs[n] = {}
             /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Quiescent

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------

TypeOK == /\ msgs \in [Node -> SUBSET IdSet]
          /\ pc \in [Node -> {"n0", "n1"}]
          /\ initiator \in [Node -> BOOLEAN]
          /\ state \in [Node -> {"cand", "lost", "won"}]

Correctness ==
  \A n \in Node : state[n] = "won" =>
     /\ initiator[n]
     /\ \A m \in Node \ {n} :
           /\ state[m] = "lost"
           /\ initiator[m] => Id[m] > Id[n]

Uniqueness ==
  \A m, n \in Node : (state[m] = "won" /\ state[n] = "won") => m = n

Liveness ==
  (\E n \in Node : initiator[n]) => <>(\E n \in Node : state[n] = "won")

Termination ==
  (\E n \in Node : initiator[n]) ~> (\E n \in Node : state[n] = "won")

=============================================================================
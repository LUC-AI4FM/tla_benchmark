---------------------------- MODULE MCChangRoberts ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

Node == 1 .. N

Id == [n \in Node |-> n]

succ(n) == IF n = N THEN 1 ELSE n + 1

-----------------------------------------------------------------------------

TypeOK ==
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ pc \in [Node -> {"n0", "n1"}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

Init ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ msgs = [n \in Node |-> {}]
  /\ state = [n \in Node |-> IF initiator[n] THEN "cand" ELSE "lost"]
  /\ pc = [n \in Node |-> "n0"]

n0(self) ==
  /\ pc[self] = "n0"
  /\ IF initiator[self]
       THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
       ELSE UNCHANGED msgs
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << initiator, state >>

n1(self) ==
  /\ pc[self] = "n1"
  /\ \E id \in msgs[self] :
       LET removed == [msgs EXCEPT ![self] = @ \ {id}]
       IN  IF id = Id[self]
             THEN /\ state' = [state EXCEPT ![self] = "won"]
                  /\ msgs' = removed
             ELSE IF id < Id[self]
                    THEN /\ state' = IF state[self] = "cand"
                                       THEN [state EXCEPT ![self] = "lost"]
                                       ELSE state
                         /\ msgs' = [removed EXCEPT ![succ(self)] = @ \cup {id}]
                    ELSE /\ msgs' = removed
                         /\ UNCHANGED state
  /\ UNCHANGED << pc, initiator >>

node(self) == n0(self) \/ n1(self)

Terminating ==
  /\ \A n \in Node : pc[n] = "n1" /\ msgs[n] = {}
  /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------

Correctness ==
  \A n \in Node :
    state[n] = "won" =>
      /\ initiator[n]
      /\ \A m \in Node \ {n} :
           /\ state[m] = "lost"
           /\ initiator[m] => Id[m] > Id[n]

Liveness ==
  (\E n \in Node : initiator[n]) => <>(\E n \in Node : state[n] = "won")

=============================================================================
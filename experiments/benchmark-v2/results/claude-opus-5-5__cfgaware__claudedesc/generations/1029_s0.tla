---------------------------- MODULE ChangRoberts ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Node == 1 .. N

\* Concrete identity assignment: process i has identity i
Id == [i \in Node |-> i]

succ(n) == IF n = N THEN 1 ELSE n + 1

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

TypeOK ==
  /\ msgs \in [Node -> SUBSET Node]
  /\ pc \in [Node -> {"n0", "n1"}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

Init ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ msgs = [n \in Node |-> {}]
  /\ pc = [n \in Node |-> "n0"]
  /\ state = [n \in Node |-> "cand"]

\* Initiators send their own identity to their successor
n0(self) ==
  /\ pc[self] = "n0"
  /\ IF initiator[self]
       THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
       ELSE UNCHANGED msgs
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED << initiator, state >>

\* Receive and process a message
n1(self) ==
  /\ pc[self] = "n1"
  /\ \E id \in msgs[self] :
       LET rmsgs == [msgs EXCEPT ![self] = @ \ {id}] IN
       IF state[self] = "lost"
         THEN \* already lost: just forward
              /\ msgs' = [rmsgs EXCEPT ![succ(self)] = @ \cup {id}]
              /\ UNCHANGED state
         ELSE IF id > Id[self]
           THEN \* larger identity: lose and forward
                /\ state' = [state EXCEPT ![self] = "lost"]
                /\ msgs' = [rmsgs EXCEPT ![succ(self)] = @ \cup {id}]
           ELSE IF id < Id[self]
             THEN \* smaller identity: swallow it; a non-initiator
                  \* joins the election by sending its own identity
                  /\ IF ~ initiator[self]
                       THEN msgs' = [rmsgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
                       ELSE msgs' = rmsgs
                  /\ UNCHANGED state
             ELSE \* own identity came back around: elected
                  /\ state' = [state EXCEPT ![self] = "won"]
                  /\ msgs' = rmsgs
  /\ UNCHANGED << pc, initiator >>

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
\* Safety: only the node with the maximum identity can win, and when it
\* wins, all other nodes have lost.
Correctness ==
  \A n \in Node :
    state[n] = "won" =>
      /\ \A m \in Node \ {n} : /\ state[m] = "lost"
                               /\ Id[m] < Id[n]

\* Liveness: if some node initiates an election, a leader is eventually elected.
Liveness ==
  (\E n \in Node : initiator[n]) => <>(\E n \in Node : state[n] = "won")

=============================================================================
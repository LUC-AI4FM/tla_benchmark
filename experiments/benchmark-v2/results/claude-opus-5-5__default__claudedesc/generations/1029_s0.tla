---------------------------- MODULE MCChangRoberts ----------------------------
(***************************************************************************)
(* Chang-Roberts leader election in a unidirectional ring of N processes. *)
(* Process i has identity i, so identities equal ring positions. Each     *)
(* process forwards only identifiers larger than its own. The process     *)
(* with the maximum identifier among the initiators sees its own          *)
(* identifier return and declares itself the leader.                      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Node == 1 .. N

\* Concrete identity assignment: process i has identity i
Id == [i \in Node |-> i]

\* Successor of a node in the unidirectional ring
succ(n) == IF n = N THEN 1 ELSE n + 1

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

-----------------------------------------------------------------------------

Init ==
    /\ initiator \in [Node -> BOOLEAN]
    /\ msgs = [n \in Node |-> {}]
    /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
    /\ pc = [self \in Node |-> "n0"]

\* An initiator sends its own identity to its successor
n0(self) ==
    /\ pc[self] = "n0"
    /\ IF initiator[self]
          THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
          ELSE msgs' = msgs
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED << initiator, state >>

\* Receive and handle a message
n1(self) ==
    /\ pc[self] = "n1"
    /\ \E id \in msgs[self] :
         LET rmsgs == [msgs EXCEPT ![self] = @ \ {id}]
         IN  IF state[self] = "lost"
                THEN /\ msgs' = [rmsgs EXCEPT ![succ(self)] = @ \cup {id}]
                     /\ state' = state
             ELSE IF id > Id[self]
                THEN /\ state' = [state EXCEPT ![self] = "lost"]
                     /\ msgs' = [rmsgs EXCEPT ![succ(self)] = @ \cup {id}]
             ELSE IF id = Id[self]
                THEN /\ state' = [state EXCEPT ![self] = "won"]
                     /\ msgs' = rmsgs
             ELSE    /\ msgs' = rmsgs        \* discard smaller identity
                     /\ state' = state
    /\ pc' = pc
    /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------

TypeOK ==
    /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
    /\ pc \in [Node -> {"n0", "n1"}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state \in [Node -> {"cand", "lost", "won"}]

\* A node that has won is an initiator, all other nodes have lost,
\* and it has the largest identity among all initiators.
Correctness ==
    \A n \in Node :
        state[n] = "won" =>
            /\ initiator[n]
            /\ \A m \in Node \ {n} : state[m] = "lost"
            /\ \A m \in Node : initiator[m] => Id[m] <= Id[n]

\* If some process initiates the election, eventually a leader is elected.
Liveness ==
    (\E n \in Node : initiator[n]) => <>(\E n \in Node : state[n] = "won")

=============================================================================
---------------------------- MODULE ChangRoberts ----------------------------
(***************************************************************************)
(* Chang-Roberts leader election on a unidirectional ring.                 *)
(* Nodes 1..N are arranged in a ring and each node sends only to its       *)
(* successor. Each node has a unique identifier Id[n]. Any subset of nodes *)
(* may be initiators. Initiators send their own identifier around the      *)
(* ring. A node that is no longer competing forwards every message. A      *)
(* candidate that receives a smaller identifier loses and forwards it. A   *)
(* candidate that receives a larger identifier discards it. A candidate    *)
(* that receives its own identifier declares itself the winner.            *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    N,      \* number of nodes in the ring
    Id      \* sequence of unique node identifiers, Id[n] is the id of node n

ASSUME NAssumption  == N \in Nat \ {0}
ASSUME IdAssumption ==
    /\ Id \in Seq(Nat)
    /\ Len(Id) = N
    /\ \A m, n \in 1..N : m # n => Id[m] # Id[n]

Nodes == 1..N

\* Successor of node n in the ring
succ(n) == IF n = N THEN 1 ELSE n + 1

VARIABLES
    msgs,       \* msgs[n]: set of identifiers in transit to node n
    initiator,  \* initiator[n]: TRUE iff node n initiates the election
    state,      \* state[n] \in {"cand", "lost", "won"}
    pc          \* pc[n] \in {"n0", "n1"}: control state of node n

vars == << msgs, initiator, state, pc >>

TypeOK ==
    /\ msgs \in [Nodes -> SUBSET {Id[n] : n \in Nodes}]
    /\ initiator \in [Nodes -> BOOLEAN]
    /\ state \in [Nodes -> {"cand", "lost", "won"}]
    /\ pc \in [Nodes -> {"n0", "n1"}]

-----------------------------------------------------------------------------
Init ==
    /\ msgs = [n \in Nodes |-> {}]
    /\ initiator \in [Nodes -> BOOLEAN]
    /\ state = [n \in Nodes |-> IF initiator[n] THEN "cand" ELSE "lost"]
    /\ pc = [n \in Nodes |-> "n0"]

\* Initiators send their own identifier to their successor.
Start(self) ==
    /\ pc[self] = "n0"
    /\ IF initiator[self]
          THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
          ELSE UNCHANGED msgs
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED << initiator, state >>

\* Receive and handle an identifier message.
Receive(self) ==
    /\ pc[self] = "n1"
    /\ \E id \in msgs[self] :
         LET rmsgs == [msgs EXCEPT ![self] = @ \ {id}]
         IN
         IF state[self] = "lost"
            THEN \* not competing: just forward
                 /\ msgs' = [rmsgs EXCEPT ![succ(self)] = @ \cup {id}]
                 /\ UNCHANGED state
         ELSE IF id < Id[self]
            THEN \* smaller id: lose and forward
                 /\ state' = [state EXCEPT ![self] = "lost"]
                 /\ msgs' = [rmsgs EXCEPT ![succ(self)] = @ \cup {id}]
         ELSE \* larger id: discard; own id: declare winner
                 /\ msgs' = rmsgs
                 /\ IF id = Id[self]
                       THEN state' = [state EXCEPT ![self] = "won"]
                       ELSE UNCHANGED state
    /\ UNCHANGED << initiator, pc >>

Node(self) == Start(self) \/ Receive(self)

Next == \E self \in Nodes : Node(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Nodes : WF_vars(Node(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* A winner must have been an initiator, and all other nodes must have lost.
Correctness ==
    \A i \in Nodes :
        state[i] = "won" =>
            /\ initiator[i]
            /\ \A j \in Nodes \ {i} : state[j] = "lost"

\* The winner has the smallest identifier among all initiators.
SmallestWins ==
    \A i \in Nodes :
        state[i] = "won" =>
            \A j \in Nodes : initiator[j] => Id[i] <= Id[j]

Safety == TypeOK /\ Correctness /\ SmallestWins

THEOREM Spec => [](TypeOK /\ Correctness /\ SmallestWins)

(***************************************************************************)
(* Liveness: if there is a candidate, eventually some node wins.           *)
(***************************************************************************)
Liveness ==
    (\E i \in Nodes : state[i] = "cand") ~> (\E i \in Nodes : state[i] = "won")

THEOREM Spec => Liveness

=============================================================================
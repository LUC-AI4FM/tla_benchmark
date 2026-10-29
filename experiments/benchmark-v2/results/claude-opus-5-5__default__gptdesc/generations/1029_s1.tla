---------------------------- MODULE MCChangRoberts ----------------------------
(***************************************************************************)
(* Model-checking module for the Chang-Roberts leader election algorithm  *)
(* on a unidirectional ring of N processes. Process i has identifier      *)
(* Id[i] = i. The node with the largest identifier becomes the leader.    *)
(* The algorithm is written out in full so that this module is            *)
(* self-contained and parses on its own.                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat

Node == 1 .. N

\* Identifier function: each process index maps to itself.
Id == [i \in Node |-> i]

\* Successor of a node on the unidirectional ring.
succ(n) == IF n = N THEN 1 ELSE n + 1

VARIABLES msgs, pc, initiator, state

vars == <<msgs, pc, initiator, state>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
    /\ pc \in [Node -> {"n0", "n1"}]
    /\ initiator \in [Node -> BOOLEAN]
    /\ state \in [Node -> {"cand", "lost", "won"}]

Init ==
    /\ initiator \in [Node -> BOOLEAN]
    /\ msgs = [n \in Node |-> {}]
    /\ pc = [n \in Node |-> "n0"]
    /\ state = [n \in Node |-> "cand"]

\* Initiators send their own identifier to their successor.
n0(self) ==
    /\ pc[self] = "n0"
    /\ IF initiator[self]
          THEN msgs' = [msgs EXCEPT ![succ(self)] = @ \cup {Id[self]}]
          ELSE UNCHANGED msgs
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED <<initiator, state>>

\* Receive a message and either forward it, win, or swallow it.
n1(self) ==
    /\ pc[self] = "n1"
    /\ \E id \in msgs[self] :
         LET rest == [msgs EXCEPT ![self] = @ \ {id}]
         IN  IF state[self] = "lost" \/ id > Id[self]
               THEN \* A larger identifier is forwarded, and this node loses.
                    /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {id}]
                    /\ state' = [state EXCEPT ![self] = "lost"]
                    /\ UNCHANGED initiator
             ELSE IF id = Id[self]
               THEN \* The node's own identifier came back, so it is the leader.
                    /\ msgs' = rest
                    /\ state' = [state EXCEPT ![self] = "won"]
                    /\ UNCHANGED initiator
             ELSE \* A smaller identifier is swallowed. A dormant node wakes up
                  \* and starts its own candidacy.
                    /\ IF ~initiator[self]
                          THEN /\ msgs' = [rest EXCEPT ![succ(self)] = @ \cup {Id[self]}]
                               /\ initiator' = [initiator EXCEPT ![self] = TRUE]
                          ELSE /\ msgs' = rest
                               /\ UNCHANGED initiator
                    /\ UNCHANGED state
    /\ UNCHANGED pc

node(self) == n0(self) \/ n1(self)

\* Explicit stuttering once the algorithm has finished, to avoid deadlock.
Terminated ==
    /\ \A n \in Node : pc[n] = "n1" /\ msgs[n] = {}
    /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminated

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
MaxId == CHOOSE m \in {Id[n] : n \in Node} : \A k \in Node : Id[k] <= m

\* At most one node is ever elected.
UniqueLeader ==
    \A m, n \in Node : state[m] = "won" /\ state[n] = "won" => m = n

\* Only the node with the maximal identifier can be elected.
Correctness ==
    \A n \in Node : state[n] = "won" => Id[n] = MaxId

Inv == TypeOK /\ UniqueLeader /\ Correctness

\* If some node initiates the election, a leader is eventually elected.
Liveness ==
    (\E n \in Node : initiator[n]) ~> (\E n \in Node : state[n] = "won")

\* Eventually no messages are left in transit.
Termination ==
    <>[](\A n \in Node : msgs[n] = {})

\* Once a node wins, it stays the leader.
LeaderStable ==
    \A n \in Node : [](state[n] = "won" => [](state[n] = "won"))

THEOREM Spec => []Inv
=============================================================================
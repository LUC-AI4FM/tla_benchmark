---------------------------- MODULE ChangRoberts ----------------------------
(***************************************************************************)
(* Chang-Roberts leader election on a unidirectional ring (CACM 1979).     *)
(* The initiator with the smallest identifier is elected as leader.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N, Id

Node == 1 .. N

ASSUME
  /\ N \in Nat \ {0}
  /\ Id \in Seq(Nat)
  /\ Len(Id) = N
  /\ \A m, n \in Node : m # n => Id[m] # Id[n]

succ(n) == IF n = N THEN 1 ELSE n + 1

VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

ProcSet == Node

Init ==
  /\ msgs = [n \in Node |-> {}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
  /\ pc = [self \in ProcSet |-> "n0"]

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
       LET newMsgs == [msgs EXCEPT ![self] = @ \ {id}] IN
         IF state[self] = "lost"
           THEN /\ msgs' = [newMsgs EXCEPT ![succ(self)] = @ \cup {id}]
                /\ UNCHANGED state
           ELSE IF id < Id[self]
                  THEN /\ state' = [state EXCEPT ![self] = "lost"]
                       /\ msgs' = [newMsgs EXCEPT ![succ(self)] = @ \cup {id}]
                  ELSE /\ msgs' = newMsgs
                       /\ IF id = Id[self]
                            THEN state' = [state EXCEPT ![self] = "won"]
                            ELSE UNCHANGED state
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED initiator

node(self) == n0(self) \/ n1(self)

Next == \E self \in Node : node(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
(* Safety *)

TypeOK ==
  /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]
  /\ pc \in [Node -> {"n0", "n1"}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

Correctness ==
  \A n \in Node :
    state[n] = "won" =>
      /\ initiator[n]
      /\ \A m \in Node : initiator[m] => Id[n] <= Id[m]
      /\ \A m \in Node \ {n} : state[m] = "lost"

(* Liveness *)

Liveness ==
  (\E n \in Node : state[n] = "cand") => <>(\E n \in Node : state[n] = "won")

THEOREM Spec => [](TypeOK /\ Correctness)
THEOREM Spec => Liveness
=============================================================================
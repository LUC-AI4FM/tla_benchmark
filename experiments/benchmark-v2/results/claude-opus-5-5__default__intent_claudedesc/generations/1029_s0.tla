------------------------------ MODULE ChangRoberts ------------------------------
(***************************************************************************)
(* Chang-Roberts leader election in a unidirectional ring.                 *)
(* N processes 1..N are arranged in a ring; process n can only send        *)
(* messages to its successor succ(n).  Every process has a unique          *)
(* identifier Id[n].  Some subset of processes (the initiators) starts the *)
(* election by sending its own identifier to its successor.                *)
(*                                                                         *)
(* When process n receives identifier m:                                   *)
(*   - non-initiator: forwards m unchanged                                 *)
(*   - initiator, m > Id[n]: forwards m and knows it has lost              *)
(*   - initiator, m < Id[n]: suppresses (swallows) the message             *)
(*   - initiator, m = Id[n]: its id went around the ring -> it is leader   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N,      \* number of processes in the ring
          Id      \* Id[n] : unique identifier of process n

Node == 1..N

ASSUME NAssumption  == N \in Nat \ {0}
ASSUME IdAssumption ==
         /\ Id \in [Node -> Nat]
         /\ \A m, n \in Node : m # n => Id[m] # Id[n]   \* identifiers are unique

succ(n) == IF n = N THEN 1 ELSE n + 1      \* clockwise neighbour
pred(n) == IF n = 1 THEN N ELSE n - 1      \* counter-clockwise neighbour

VARIABLES
  initiator,   \* initiator[n] : TRUE iff process n initiated the election
  state,       \* state[n] \in {"cand", "lost", "won"}
  msgs         \* msgs[n] : FIFO channel of identifiers in transit to process n

vars == << initiator, state, msgs >>

-----------------------------------------------------------------------------

TypeOK ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]
  /\ msgs \in [Node -> Seq(Nat)]

(* Any subset of processes may initiate. Each initiator has sent its own  *)
(* identifier to its successor.  Non-initiators are never candidates.     *)
Init ==
  /\ initiator \in [Node -> BOOLEAN]
  /\ state = [n \in Node |-> IF initiator[n] THEN "cand" ELSE "lost"]
  /\ msgs  = [n \in Node |-> IF initiator[pred(n)]
                               THEN << Id[pred(n)] >>
                               ELSE << >>]

(* Process n handles the first message of its incoming channel. *)
Receive(n) ==
  /\ msgs[n] # << >>
  /\ LET m    == Head(msgs[n])
         rest == Tail(msgs[n])
     IN
       IF initiator[n]
         THEN
           \/ /\ m < Id[n]                      \* suppress smaller id
              /\ msgs'  = [msgs EXCEPT ![n] = rest]
              /\ UNCHANGED state
           \/ /\ m > Id[n]                      \* forward larger id, lose
              /\ state' = [state EXCEPT ![n] = "lost"]
              /\ msgs'  = [msgs EXCEPT ![n] = rest,
                                       ![succ(n)] = Append(@, m)]
           \/ /\ m = Id[n]                      \* own id returned: win
              /\ state' = [state EXCEPT ![n] = "won"]
              /\ msgs'  = [msgs EXCEPT ![n] = rest]
         ELSE                                   \* non-initiator relays
           /\ state' = [state EXCEPT ![n] = "lost"]
           /\ msgs'  = [msgs EXCEPT ![n] = rest,
                                    ![succ(n)] = Append(@, m)]
  /\ UNCHANGED initiator

Next == \E n \in Node : Receive(n)

Fairness == \A n \in Node : WF_vars(Receive(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

Leaders == {n \in Node : state[n] = "won"}

\* At most one process is ever elected leader
UniqueLeader == Cardinality(Leaders) <= 1

\* A leader must be the initiator with the highest identifier
LegitimateLeader ==
  \A n \in Node :
     state[n] = "won" =>
        /\ initiator[n]
        /\ \A m \in Node : initiator[m] => Id[m] <= Id[n]

\* Channels never hold more than N messages (bounds the state space)
BoundedChannels == \A n \in Node : Len(msgs[n]) <= N

Safety == TypeOK /\ UniqueLeader /\ LegitimateLeader

(* Liveness properties *)

\* If at least one process initiates, eventually some process is elected
GuaranteedElection ==
  (\E n \in Node : initiator[n]) ~> (\E n \in Node : state[n] = "won")

\* Equivalent formulation as an eventuality from the initial state
EventuallyElected ==
  (\E n \in Node : initiator[n]) => <>(\E n \in Node : state[n] = "won")

\* Once elected, a leader remains leader
StableLeader == \A n \in Node : [](state[n] = "won" => [](state[n] = "won"))

THEOREM Spec => [](TypeOK /\ UniqueLeader /\ LegitimateLeader)
THEOREM Spec => GuaranteedElection
=============================================================================
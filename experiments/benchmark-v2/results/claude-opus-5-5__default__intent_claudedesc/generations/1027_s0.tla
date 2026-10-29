---------------------------- MODULE RingLeaderElection ----------------------------
(***************************************************************************)
(* Leader election in a unidirectional ring (Chang-Roberts style).         *)
(* Processes 1..N are arranged in a ring; process n sends only to          *)
(* succ(n). Each process has a unique identifier Id[n]. Any subset of      *)
(* processes may be initiators. Each initiator injects its identifier.     *)
(* A candidate that receives a larger identifier forwards it and drops     *)
(* out. A candidate that receives a smaller identifier drops (swallows)    *)
(* it. A candidate that receives its own identifier is elected leader.     *)
(* A non-initiator (or a process that dropped out) forwards everything.    *)
(* The initiator with the maximum identifier is elected.                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,    \* number of processes in the ring
          Id    \* Id[n] is the unique identifier of process n

Node == 1 .. N

ASSUME NAssumption  == N \in Nat \ {0}
ASSUME IdAssumption ==
    /\ Id \in [Node -> Nat]
    /\ \A m, n \in Node : m # n => Id[m] # Id[n]

succ(n) == IF n = N THEN 1 ELSE n + 1
pred(n) == IF n = 1 THEN N ELSE n - 1

VARIABLES
    initiator,  \* initiator[n] : whether n participates in the election
    state,      \* "cand", "lost", or "won"
    msgs        \* msgs[n] : identifiers in transit to process n

vars == << initiator, state, msgs >>

Initiators == { n \in Node : initiator[n] }

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

-----------------------------------------------------------------------------
TypeOK ==
    /\ initiator \in [Node -> BOOLEAN]
    /\ state \in [Node -> {"cand", "lost", "won"}]
    /\ msgs \in [Node -> SUBSET {Id[n] : n \in Node}]

(* Any subset of processes may spontaneously decide to initiate; each    *)
(* initiator injects its identifier into the channel to its successor.  *)
Init ==
    /\ initiator \in [Node -> BOOLEAN]
    /\ state = [n \in Node |-> IF initiator[n] THEN "cand" ELSE "lost"]
    /\ msgs  = [n \in Node |-> IF initiator[pred(n)]
                                  THEN {Id[pred(n)]} ELSE {}]

(* Process n receives identifier id from its predecessor. *)
Receive(n, id) ==
    LET removed   == [msgs EXCEPT ![n] = @ \ {id}]
        forwarded == [removed EXCEPT ![succ(n)] = @ \cup {id}]
    IN
    /\ id \in msgs[n]
    /\ IF state[n] = "cand"
          THEN IF id = Id[n]
                  THEN \* own id returned: n is the leader
                       /\ state' = [state EXCEPT ![n] = "won"]
                       /\ msgs'  = removed
                  ELSE IF id > Id[n]
                          THEN \* larger id: forward it and drop out
                               /\ state' = [state EXCEPT ![n] = "lost"]
                               /\ msgs'  = forwarded
                          ELSE \* smaller id: swallow it
                               /\ state' = state
                               /\ msgs'  = removed
          ELSE \* non-candidate: just relay
               /\ state' = state
               /\ msgs'  = forwarded
    /\ UNCHANGED initiator

Next == \E n \in Node : \E id \in msgs[n] : Receive(n, id)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: at most one leader. *)
UniqueLeader ==
    \A m, n \in Node : (state[m] = "won" /\ state[n] = "won") => m = n

(* Correctness of the winner: the leader has the maximum identifier *)
(* among all initiators.                                            *)
CorrectWinner ==
    \A n \in Node :
        state[n] = "won" =>
            /\ initiator[n]
            /\ Id[n] = Max({Id[m] : m \in Initiators})

(* Liveness: if some process initiates, a leader is eventually elected. *)
LeaderElected ==
    (Initiators # {}) => <>(\E n \in Node : state[n] = "won")

(* Once elected, a leader stays leader. *)
LeaderStable ==
    \A n \in Node : [](state[n] = "won" => [](state[n] = "won"))

THEOREM Spec => [](TypeOK /\ UniqueLeader /\ CorrectWinner)
THEOREM Spec => LeaderElected
=============================================================================
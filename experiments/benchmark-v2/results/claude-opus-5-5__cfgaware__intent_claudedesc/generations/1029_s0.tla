---------------------------- MODULE ChangRoberts ----------------------------
(***************************************************************************)
(* Chang-Roberts leader election in a unidirectional ring.                 *)
(* Processes 1..N are arranged in a ring; process n sends to succ(n).      *)
(* Each process has a unique identifier Id[n]. A nondeterministically      *)
(* chosen subset of processes initiate the election. The initiator with    *)
(* the maximal identifier is elected.                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Nodes == 1 .. N

\* A fixed permutation of 1..N serving as unique identifiers
Id == [n \in Nodes |-> ((n + 1) % N) + 1]

succ(n) == IF n = N THEN 1 ELSE n + 1
pred(n) == IF n = 1 THEN N ELSE n - 1

VARIABLES
    initiator,  \* set of processes that initiated the election
    state,      \* state of each process: "cand", "lost", "won"
    msgs        \* msgs[n]: FIFO channel of identifiers incoming to n

vars == << initiator, state, msgs >>

TypeOK ==
    /\ initiator \subseteq Nodes
    /\ state \in [Nodes -> {"cand", "lost", "won"}]
    /\ msgs \in [Nodes -> Seq(Nodes)]

Init ==
    /\ initiator \in SUBSET Nodes
    /\ state = [n \in Nodes |-> IF n \in initiator THEN "cand" ELSE "lost"]
    \* each initiator has already sent its own identifier to its successor
    /\ msgs = [n \in Nodes |-> IF pred(n) \in initiator
                                 THEN << Id[pred(n)] >>
                                 ELSE << >>]

\* Non-initiator: forward every message unchanged
Forward(n) ==
    /\ n \notin initiator
    /\ msgs[n] # << >>
    /\ LET m == Head(msgs[n]) IN
         IF succ(n) = n
           THEN msgs' = [msgs EXCEPT ![n] = Append(Tail(@), m)]
           ELSE msgs' = [msgs EXCEPT ![n] = Tail(@),
                                     ![succ(n)] = Append(@, m)]
    /\ UNCHANGED << initiator, state >>

\* Initiator receives a smaller identifier: suppress it
Discard(n) ==
    /\ n \in initiator
    /\ msgs[n] # << >>
    /\ Head(msgs[n]) < Id[n]
    /\ msgs' = [msgs EXCEPT ![n] = Tail(@)]
    /\ UNCHANGED << initiator, state >>

\* Initiator receives a larger identifier: forward it and lose
Pass(n) ==
    /\ n \in initiator
    /\ msgs[n] # << >>
    /\ Head(msgs[n]) > Id[n]
    /\ LET m == Head(msgs[n]) IN
         IF succ(n) = n
           THEN msgs' = [msgs EXCEPT ![n] = Append(Tail(@), m)]
           ELSE msgs' = [msgs EXCEPT ![n] = Tail(@),
                                     ![succ(n)] = Append(@, m)]
    /\ state' = [state EXCEPT ![n] = "lost"]
    /\ UNCHANGED initiator

\* Initiator receives its own identifier: it is elected
Win(n) ==
    /\ n \in initiator
    /\ msgs[n] # << >>
    /\ Head(msgs[n]) = Id[n]
    /\ msgs' = [msgs EXCEPT ![n] = Tail(@)]
    /\ state' = [state EXCEPT ![n] = "won"]
    /\ UNCHANGED initiator

\* Termination: all channels empty, stutter to avoid deadlock
Done ==
    /\ \A n \in Nodes : msgs[n] = << >>
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes : Forward(n) \/ Discard(n) \/ Pass(n) \/ Win(n)
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Properties

UniqueLeader ==
    \A i, j \in Nodes : (state[i] = "won" /\ state[j] = "won") => i = j

LegitimateLeader ==
    \A i \in Nodes : state[i] = "won" =>
        (i \in initiator /\ \A j \in initiator : Id[j] <= Id[i])

Correctness == UniqueLeader /\ LegitimateLeader

Liveness == (initiator # {}) ~> (\E i \in Nodes : state[i] = "won")

=============================================================================
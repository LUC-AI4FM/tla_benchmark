-------------------------- MODULE PrisonersAndSwitches --------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, Counter
ASSUME  /\ N \in 1..MaxInt
        /\ N > 1
        /\ Counter \in 1..N

Prisoners == 1..N
NonCounters == Prisoners \ {Counter}

VARIABLES switchA, switchB, count, timesFlippedA, visited, done

vars == <<switchA, switchB, count, timesFlippedA, visited, done>>

TypeOK ==
    /\ switchA \in BOOLEAN
    /\ switchB \in BOOLEAN
    /\ count \in 0..(2*(N-1))
    /\ timesFlippedA \in [NonCounters -> 0..2]
    /\ visited \subseteq Prisoners
    /\ done \in BOOLEAN

Init ==
    /\ switchA = FALSE
    /\ switchB = FALSE
    /\ count = 0
    /\ timesFlippedA = [p \in NonCounters |-> 0]
    /\ visited = {}
    /\ done = FALSE

(* Action for the counter entering the room. *)
CounterAction ==
    /\ \/ /\ switchA
          /\ count' = count + 1
          /\ switchA' = FALSE
       \/ /\ ~switchA
          /\ UNCHANGED <<count, switchA>>
    /\ IF count' = 2 * (N - 1)
       THEN done' = TRUE
       ELSE UNCHANGED done
    /\ UNCHANGED timesFlippedA

(* Action for a non-counter prisoner p entering the room. *)
NonCounterAction(p) ==
    /\ \/ /\ ~switchA /\ timesFlippedA[p] < 2
          /\ switchA' = TRUE
          /\ timesFlippedA' = [timesFlippedA EXCEPT ![p] = @ + 1]
       \/ /\ \/ switchA
             \/ timesFlippedA[p] = 2
          /\ UNCHANGED <<switchA, timesFlippedA>>
    /\ UNCHANGED <<count, done>>

(* A prisoner p is chosen to enter the room. *)
Enter(p) ==
    /\ visited' = visited \cup {p}
    /\ switchB' = ~switchB
    /\ IF p = Counter
       THEN CounterAction
       ELSE NonCounterAction(p)

Next == \E p \in Prisoners : Enter(p)

(* Fairness requires every prisoner to be brought to the room infinitely often. *)
Fairness == \A p \in Prisoners : WF_vars(Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* SAFETY: When the protocol declares completion, every prisoner has visited.
Safety == done => (visited = Prisoners)

\* LIVENESS: The protocol eventually declares completion.
Liveness == <>done

=============================================================================
MODULE PrisonersSwitch

EXTENDS Naturals, Sequences, TLC

CONSTANTS N, COUNTER
ASSUME COUNTER \in 1..N

VARIABLE switchA, switchB,
        upCount, count, visited, done

vars == <<switchA, switchB, upCount, count, visited, done>>

Init ==
    /\ switchA = FALSE
    /\ switchB = FALSE
    /\ upCount   = [i \in 1..N |-> 0]
    /\ count     = 0
    /\ visited   = [i \in 1..N |-> FALSE]
    /\ done      = FALSE

CounterStep(i) ==
    /\ i = COUNTER
    /\ IF switchA THEN
          /\ switchA' = FALSE
          /\ count'   = count + 1
       ELSE
          /\ switchA' = switchA
          /\ count'   = count
    /\ switchB' = NOT switchB
    /\ upCount' = upCount
    /\ visited' = [visited EXCEPT ![i] = TRUE]
    /\ done'    = done

NonCounterStep(i) ==
    /\ i \in 1..N /\ i # COUNTER
    /\ IF switchA = FALSE /\ upCount[i] < 2 THEN
          /\ switchA' = TRUE
          /\ upCount' = [upCount EXCEPT ![i] = upCount[i] + 1]
       ELSE
          /\ switchA' = switchA
          /\ upCount' = upCount
    /\ switchB' = NOT switchB
    /\ count'   = count
    /\ visited' = [visited EXCEPT ![i] = TRUE]
    /\ done'    = done

Declare ==
    /\ ~done
    /\ count >= N-1
    /\ done' = TRUE
    /\ UNCHANGED <<switchA, switchB, upCount, count, visited>>

Step(i) == CounterStep(i) \/ NonCounterStep(i)

Next ==
    \/ \E i \in 1..N : Step(i)
    \/ Declare

Safety ==
    [] (done => \A i \in 1..N : visited[i])

Liveness ==
    <> done

Spec ==
    Init /\ [][Next]_vars /\ Safety /\ Liveness

(* Fairness assumptions: each prisoner is brought into the room infinitely often *)
WF_0 (\E i \in 1..N : Step(i))

*END
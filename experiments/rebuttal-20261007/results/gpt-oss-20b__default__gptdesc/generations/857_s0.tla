MODULE PrisonerLightSwitch

EXTENDS Naturals, Sequences, SETS

CONSTANTS N, UNKNOWN_INIT, COUNTER

(* Variables *)
VARIABLES lamp, counterVal, visited, signaledCount, victory

(* Derived constants *)
Threshold == IF UNKNOWN_INIT THEN 2*N - 1 ELSE N
MaxSignal   == IF UNKNOWN_INIT THEN 2 ELSE 1

Init ==
    /\ lamp = IF UNKNOWN_INIT THEN CHOOSE l ∈ BOOLEAN : l ELSE FALSE
    /\ counterVal = 0
    /\ victory = FALSE
    /\ visited = [i \in 1..N |-> FALSE]
    /\ signaledCount = [i \in 1..N |-> 0]

NonCounterAction(i) ==
    /\ i ∈ 1..N
    /\ i ≠ COUNTER
    /\ visited'   = [visited EXCEPT ![i] = TRUE]
    /\ lamp'      = IF lamp = FALSE /\ signaledCount[i] < MaxSignal THEN TRUE ELSE lamp
    /\ signaledCount' =
          IF lamp = FALSE /\ signaledCount[i] < MaxSignal
          THEN [signaledCount EXCEPT ![i] = signaledCount[i] + 1]
          ELSE signaledCount
    /\ counterVal' = counterVal
    /\ victory'   = IF (counterVal >= Threshold) /\ ∀ j ∈ 1..N : visited[j] THEN TRUE ELSE victory

CounterAction(i) ==
    /\ i ∈ 1..N
    /\ i = COUNTER
    /\ visited'   = [visited EXCEPT ![COUNTER] = TRUE]
    /\ lamp'      = IF lamp = TRUE THEN FALSE ELSE lamp
    /\ counterVal' =
          IF lamp = TRUE THEN counterVal + 1 ELSE counterVal
    /\ signaledCount' = signaledCount
    /\ victory'   = IF (counterVal' >= Threshold) /\ ∀ j ∈ 1..N : visited'[j] THEN TRUE ELSE victory

PrisonerAction(i) == NonCounterAction(i) \/ CounterAction(i)

Next == ∃ i ∈ 1..N : PrisonerAction(i)

Inv == victory => ∀ j ∈ 1..N : visited[j] = TRUE

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Inv

=============================================================================
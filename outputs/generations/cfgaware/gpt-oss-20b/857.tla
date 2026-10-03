------------------------------ MODULE PrisonerLightSwitch ------------------------------
EXTENDS Naturals

CONSTANTS N, Counter, UnknownInit

(* Variant parameters *)
maxSignal == IF UnknownInit THEN 2 ELSE 1
threshold   == IF UnknownInit THEN 2*N - 1 ELSE N-1

VARIABLES lamp, count, visited, announced, signals

(* --------------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ (UnknownInit => lamp ∈ {TRUE, FALSE})
  /\ (~UnknownInit => lamp = FALSE)
  /\ count   = 0
  /\ visited = {}
  /\ announced = FALSE
  /\ signals = [i \in 1..N |-> 0]

(* --------------------------------------------------------------------------- *)
(* Counter's action *)
CounterAction(i) ==
  /\ i = Counter
  /\ lamp'     = IF lamp THEN FALSE ELSE lamp
  /\ count'    = IF lamp THEN count + 1 ELSE count
  /\ visited'  = visited ∪ {i}
  /\ announced'= IF count' >= threshold THEN TRUE ELSE announced
  /\ signals'  = signals

(* --------------------------------------------------------------------------- *)
(* Non‑counter's action *)
NonCounterAction(i) ==
  /\ i ≠ Counter
  /\ visited'  = visited ∪ {i}
  /\ lamp'     = IF lamp = FALSE /\ signals[i] < maxSignal THEN TRUE ELSE lamp
  /\ signals'  = [signals EXCEPT ![i] = IF lamp = FALSE /\ signals[i] < maxSignal THEN signals[i] + 1 ELSE signals[i]]
  /\ count'    = count
  /\ announced'= announced

(* --------------------------------------------------------------------------- *)
(* Action of selecting a prisoner *)
Select ==
  ∃ i \in 1..N :
      CounterAction(i) \/ NonCounterAction(i)

Next == Select

Spec == Init /\ [][Next]_vars /\ TypeOK

(*
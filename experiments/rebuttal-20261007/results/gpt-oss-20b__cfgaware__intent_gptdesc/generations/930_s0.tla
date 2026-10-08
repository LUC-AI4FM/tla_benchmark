MODULE Clock12
IMPORTS Naturals, TLC

VARIABLES HC

(* The set of valid hour values *)
Hours == 1 .. 12

(* Initial condition: the clock starts with a valid hour value *)
HCini == HC ∈ Hours

(* Transition relation: advance by one hour modulo 12 *)
Next ==
  /\ HC' = IF HC = 12 THEN 1 ELSE HC + 1

(* Invariant: the hour is always within 1..12 *)
Inv == HC ∈ Hours

(* Liveness property: each hour occurs infinitely often under strong fairness *)
Recurrence ==
  \A h \in Hours : []<> (HC = h)

(* Strong fairness assumption for the step relation *)
Fairness == WF_vars(Next)

(* Full specification including initialization, transition, and fairness *)
Spec == HCini /\ [][Next]_<<HC>> /\ Fairness

THEOREM InitPreservesInv:
  Spec => [] Inv

THEOREM StepCorrect:
  Spec => [] (Next => (HC' = IF HC = 12 THEN 1 ELSE HC + 1))

THEOREM RecurrenceTheorem:
  Spec => Recurrence

END Clock12
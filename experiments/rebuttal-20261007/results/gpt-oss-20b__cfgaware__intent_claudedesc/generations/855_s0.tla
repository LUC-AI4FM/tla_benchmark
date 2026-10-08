------------------------------ MODULE PrisonersPuzzle ------------------------------
EXTENDS Naturals, TLC, FiniteSets

CONSTANTS Prisoner, p2, p3
ASSUME p2 ∈ Prisoner /\ p3 ∈ Prisoner

(* Derived constant: the counter *)
Counter == CHOOSE x \in Prisoner : x # p2 /\ x # p3

VARIABLES turn, s1, s2, count, declared, flipped

(* Initial state *)
Init ==
  /\ s1 ∈ BOOLEAN
  /\ s2 ∈ BOOLEAN
  /\ count = 0
  /\ declared = FALSE
  /\ flipped = {}
  /\ turn ∈ Prisoner

(* Action when a prisoner is selected and flips a switch *)
ActionSelect(p) ==
  /\ turn' = p
  /\ IF p = Counter THEN
        (* counter's action *)
        IF s1 THEN
            s1' = FALSE /\ s2' = s2 /\ count' = count + 1 /\ flipped' = flipped
        ELSE
            s1' = s1 /\ s2' = ¬s2 /\ count' = count /\ flipped' = flipped
      ELSE
        (* non-counter action *)
        IF s1 = FALSE ∧ p ∉ flipped THEN
            s1' = TRUE /\ s2' = s2 /\ count' = count + 1 /\ flipped' = flipped ∪ {p}
        ELSE
            s1' = s1 /\ s2' = ¬s2 /\ count' = count /\ flipped' = flipped
  /\ declared' = declared

(* Action for the counter to declare completion *)
Declare ==
  /\ turn = Counter
  /\ declared = FALSE
  /\ count = 2
  /\ declared' = TRUE
  /\ turn' = turn
  /\ s1' = s1
  /\ s2' = s2
  /\ count' = count
  /\ flipped' = flipped

Next ==
  ∃ p \in Prisoner : ActionSelect(p) \/ Declare

(* Specification *)
Spec == Init /\ [][Next]_vars

(* Type invariant *)
TypeOK ==
  /\ turn ∈ Prisoner
  /\ s1 ∈ BOOLEAN
  /\ s2 ∈ BOOLEAN
  /\ count ∈ Nat
  /\ declared ∈ BOOLEAN
  /\ flipped ⊆ Prisoner

(* Count invariant: number of flips equals number of distinct non-counters who have flipped *)
CountInvariant == count = Cardinality(flipped)

(* Safety property: if counter declares, all non-counters have flipped the designated switch at least once *)
Safety == [] (declared ⇒ (p2 ∈ flipped /\ p3 ∈ flipped))

(* Liveness property: eventually the counter will declare completion *)
Liveness == <> declared

=============================================================================
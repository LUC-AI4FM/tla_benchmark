----------------------------- MODULE PrisonersAndSwitches -----------------------------
EXTENDS Naturals, FiniteSets

(*
  Constants expected to be bound by the model:
  - Prisoner: a finite nonempty set of prisoner identifiers
  - p2, p3: distinct elements of Prisoner
*)
CONSTANTS Prisoner, p2, p3

ASSUME /\ p2 \in Prisoner
       /\ p3 \in Prisoner
       /\ p2 # p3
       /\ IsFiniteSet(Prisoner)

(*
  Designate p2 as the counter.
*)
Counter == p2
NonCounter == Prisoner \ {Counter}

VARIABLES switchA, switchB, count, quota, visited

vars == << switchA, switchB, count, quota, visited >>

Init ==
  /\ switchA = FALSE
  /\ switchB = FALSE
  /\ count = 0
  /\ quota = [p \in Prisoner |-> 0]
  /\ visited = {}

(*
  Step(p): prisoner p performs one visit to the room.
  - Counter:
      If A is up, lower it and increment count; otherwise flip B.
  - Non-counter:
      If A is down and p has quota < 2, raise A and consume one quota; otherwise flip B.
  In all cases, record p as visited.
*)
Step(p) ==
  /\ p \in Prisoner
  /\ CASE p = Counter /\ switchA ->
         /\ switchA' = FALSE
         /\ count'   = count + 1
         /\ switchB' = switchB
         /\ quota'   = quota
     [] p = Counter /\ ~switchA ->
         /\ switchA' = switchA
         /\ count'   = count
         /\ switchB' = ~switchB
         /\ quota'   = quota
     [] p # Counter /\ ~switchA /\ quota[p] < 2 ->
         /\ switchA' = TRUE
         /\ count'   = count
         /\ switchB' = switchB
         /\ quota'   = [quota EXCEPT ![p] = @ + 1]
     [] OTHER ->
         /\ switchA' = switchA
         /\ count'   = count
         /\ switchB' = ~switchB
         /\ quota'   = quota
  /\ visited' = visited \cup {p}

Next == \E p \in Prisoner: Step(p)

Done == count = 2 * Cardinality(NonCounter)

AllVisited == visited = Prisoner

TypeOK ==
  /\ switchA \in BOOLEAN
  /\ switchB \in BOOLEAN
  /\ count \in 0 .. (2 * Cardinality(NonCounter))
  /\ quota \in [Prisoner -> 0..2]
  /\ visited \subseteq Prisoner
  /\ Counter \in Prisoner
  /\ p3 \in Prisoner

CountInvariant ==
  count <= 2 * Cardinality(NonCounter)

Safety ==
  [](Done => AllVisited)

Liveness ==
  <>Done

Spec ==
  Init /\ [][Next]_vars /\ \A p \in Prisoner: WF_vars(Step(p))

=============================================================================
---- MODULE PrisonersBulb ----
EXTENDS Naturals

CONSTANTS
  N,           \* Number of prisoners, N >= 2
  Counter,     \* The distinguished counting prisoner (an element of 1..N)
  UnknownInit  \* BOOLEAN: FALSE => lamp initially known OFF, TRUE => unknown

(*
  Domain of prisoners and strategy parameters.
  BudgetLimit = number of OFF->ON signals allowed to each non-counter.
  Target = count threshold for a correct announcement.
    - If UnknownInit = FALSE: BudgetLimit = 1, Target = N-1.
    - If UnknownInit = TRUE:  BudgetLimit = 2, Target = 2*(N-1).
*)
P == 1..N
BudgetLimit == IF UnknownInit THEN 2 ELSE 1
Target == (N - 1) * BudgetLimit

VARIABLES
  lamp,        \* BOOLEAN: shared lamp (OFF = FALSE, ON = TRUE)
  tokens,      \* [P -> 0..BudgetLimit]: remaining OFF->ON signals for each prisoner
  visited,     \* SUBSET P: prisoners who have visited at least once
  count,       \* Nat: number of ON->OFF events performed by Counter
  announced    \* BOOLEAN: whether the final announcement has been made

vars == << lamp, tokens, visited, count, announced >>

Init ==
  /\ Counter \in P
  /\ visited = {}
  /\ tokens \in [P -> 0..BudgetLimit]
  /\ tokens = [i \in P |-> IF i = Counter THEN 0 ELSE BudgetLimit]
  /\ count = 0
  /\ announced = FALSE
  /\ IF UnknownInit THEN lamp \in BOOLEAN ELSE lamp = FALSE

Visit(p) ==
  /\ ~announced
  /\ count < Target
  /\ p \in P
  /\ visited' = visited \cup {p}
  /\ lamp' =
       IF p = Counter THEN
         IF lamp THEN FALSE ELSE lamp
       ELSE
         IF (~lamp) /\ (tokens[p] > 0) THEN TRUE ELSE lamp
  /\ count' =
       IF (p = Counter) /\ lamp THEN count + 1 ELSE count
  /\ tokens' =
       [tokens EXCEPT
         ![p] =
           IF (p # Counter) /\ (~lamp) /\ (tokens[p] > 0)
             THEN @ - 1
             ELSE @]
  /\ announced' = announced

Announce ==
  /\ ~announced
  /\ count = Target
  /\ announced' = TRUE
  /\ UNCHANGED << lamp, tokens, visited, count >>

Next ==
  \/ \E p \in P: Visit(p)
  \/ Announce

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in P: SF_vars(Visit(p))

TypeOK ==
  /\ Counter \in P
  /\ lamp \in BOOLEAN
  /\ tokens \in [P -> 0..BudgetLimit]
  /\ tokens[Counter] = 0
  /\ visited \subseteq P
  /\ count \in 0..Target
  /\ announced \in BOOLEAN

VictoryOK ==
  announced => (visited = P)

Terminating ==
  <>announced

====
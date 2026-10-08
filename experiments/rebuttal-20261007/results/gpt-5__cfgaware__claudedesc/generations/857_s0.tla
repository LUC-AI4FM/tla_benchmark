------------------------------ MODULE PrisonersLamp ------------------------------

EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS
  Prisoner,
  Light_Unknown

VARIABLES
  count,       \* counter's running count
  announced,   \* has victory been announced
  signals,     \* how many times each prisoner has signalled (turned light on)
  light,       \* current lamp state
  visited      \* warden's ground-truth set of prisoners who have visited

Counter == CHOOSE p \in Prisoner: TRUE

N == Cardinality(Prisoner)

Threshold == IF Light_Unknown THEN 2*N - 1 ELSE N

MaySignalLimit(p) == IF p = Counter THEN 0 ELSE IF Light_Unknown THEN 2 ELSE 1

vars == << count, announced, signals, light, visited >>

TypeOK ==
  /\ Counter \in Prisoner
  /\ count \in 1..Threshold
  /\ announced \in BOOLEAN
  /\ light \in BOOLEAN
  /\ visited \subseteq Prisoner
  /\ signals \in [Prisoner -> Nat]
  /\ \A p \in Prisoner: signals[p] \in 0..MaySignalLimit(p)

Init ==
  /\ count = 1
  /\ announced = FALSE
  /\ IF Light_Unknown THEN light \in BOOLEAN ELSE light = FALSE
  /\ visited = {}
  /\ signals = [p \in Prisoner |-> 0]

Visit(p) ==
  /\ p \in Prisoner
  /\ ~announced
  /\ LET willSignal ==
         /\ p # Counter
         /\ ~light
         /\ signals[p] < MaySignalLimit(p)
     lightNext ==
         IF p = Counter
           THEN IF light THEN FALSE ELSE light
           ELSE IF willSignal THEN TRUE ELSE light
     signalsNext ==
         [signals EXCEPT ![p] =
           IF p = Counter THEN @
           ELSE IF willSignal THEN @ + 1 ELSE @]
     countNext ==
         IF (p = Counter) /\ light THEN count + 1 ELSE count
     IN
     /\ visited' = visited \cup {p}
     /\ light' = lightNext
     /\ signals' = signalsNext
     /\ count' = countNext
     /\ announced' = announced \/ (countNext = Threshold)

Next ==
  \/ \E p \in Prisoner: Visit(p)
  \/ /\ announced
     /\ UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Prisoner: WF_vars(Visit(p))

VictoryOK == announced => visited = Prisoner

Terminating == <>announced

===============================================================================
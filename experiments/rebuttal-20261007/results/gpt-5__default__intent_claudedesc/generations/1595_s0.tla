---------------------------- MODULE FairCounter ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N
ASSUME N = 10

VARIABLES c, seen

Init ==
  /\ c = 0
  /\ seen = {}

Inc ==
  /\ c < N
  /\ c' = c + 1
  /\ seen' = seen \cup {c}

Next == Inc

Vars == << c, seen >>

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ WF_Vars(Inc)

TypeOK ==
  /\ c \in 0..N
  /\ seen \subseteq 0..N

ExactlySeen ==
  seen = 0..(c - 1)

NoRepeat ==
  c \notin seen

Termination ==
  <> (c = N)

Visit5 ==
  <> (c = 5)

AboutTo10 ==
  /\ c = N - 1
  /\ ENABLED Inc

VisitAboutTo10 ==
  <> AboutTo10

============================================================================
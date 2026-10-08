------------------------------ MODULE EvenOddMutualRecursion ------------------------------

EXTENDS Naturals, TLC

CONSTANTS N

ASSUME N \in Nat /\ N = 6

VARIABLES proc, n, result, oddEntries, evenToOdd, printed

ProcVals == {"Main", "Even", "Odd", "Done"}

vars == << proc, n, result, oddEntries, evenToOdd, printed >>

Init ==
  /\ proc = "Main"
  /\ n = 0
  /\ result \in BOOLEAN
  /\ oddEntries = 0
  /\ evenToOdd = 0
  /\ printed = FALSE

CallEven ==
  /\ proc = "Main"
  /\ proc' = "Even"
  /\ n' = N
  /\ UNCHANGED << result, oddEntries, evenToOdd, printed >>

EvenBase ==
  /\ proc = "Even"
  /\ n = 0
  /\ proc' = "Done"
  /\ result' = TRUE
  /\ n' = n
  /\ UNCHANGED << oddEntries, evenToOdd, printed >>

EvenRecur ==
  /\ proc = "Even"
  /\ n > 0
  /\ proc' = "Odd"
  /\ n' = n - 1
  /\ oddEntries' = oddEntries + 1
  /\ evenToOdd' = evenToOdd + 1
  /\ UNCHANGED << result, printed >>

OddBase ==
  /\ proc = "Odd"
  /\ n = 0
  /\ proc' = "Done"
  /\ result' = FALSE
  /\ n' = n
  /\ UNCHANGED << oddEntries, evenToOdd, printed >>

OddRecur ==
  /\ proc = "Odd"
  /\ n > 0
  /\ proc' = "Even"
  /\ n' = n - 1
  /\ UNCHANGED << result, oddEntries, evenToOdd, printed >>

Print ==
  /\ proc = "Done"
  /\ printed = FALSE
  /\ printed' = TRUE
  /\ UNCHANGED << proc, n, result, oddEntries, evenToOdd >>

Next ==
  CallEven \/ EvenBase \/ EvenRecur \/ OddBase \/ OddRecur \/ Print

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CallEven)
  /\ WF_vars(EvenBase)
  /\ WF_vars(EvenRecur)
  /\ WF_vars(OddBase)
  /\ WF_vars(OddRecur)
  /\ WF_vars(Print)

Termination ==
  <> (printed = TRUE)

TypeInv ==
  /\ proc \in ProcVals
  /\ n \in Nat
  /\ result \in BOOLEAN
  /\ oddEntries \in Nat
  /\ evenToOdd \in Nat
  /\ printed \in BOOLEAN

CountEquality ==
  oddEntries = evenToOdd

BoundInv ==
  /\ oddEntries <= 3
  /\ evenToOdd <= 3

EndCountsExact ==
  printed => /\ oddEntries = 3 /\ evenToOdd = 3

EndResultCorrect ==
  printed => result = TRUE

SafetyInv ==
  /\ TypeInv
  /\ CountEquality
  /\ BoundInv
  /\ EndCountsExact
  /\ EndResultCorrect

EndPattern ==
  <> (printed /\ oddEntries = 3 /\ evenToOdd = 3)

=============================================================================
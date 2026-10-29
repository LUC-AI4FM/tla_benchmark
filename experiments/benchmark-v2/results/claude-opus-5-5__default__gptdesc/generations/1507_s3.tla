---- MODULE CoverageRecursive ----
EXTENDS Naturals

VARIABLES clock

vars == <<clock>>

\* Recursive operator: checks a Boolean value by recursing down n steps.
RECURSIVE Check(_, _)
Check(b, n) == IF n = 0 THEN b \in BOOLEAN ELSE Check(b, n - 1)

\* Recursive operator: flips a Boolean value n times.
RECURSIVE Flip(_, _)
Flip(b, n) == IF n = 0 THEN b ELSE Flip(~b, n - 1)

TypeOK == Check(clock, 3)

\* Note: TLC's coverage reporting attributes the evaluations of the
\* recursive call Flip appearing in Init to the operator's definition
\* rather than to the call site in Init.
Init == clock = Flip(FALSE, 2)

\* A constraint-like state predicate (usable as a TLC CONSTRAINT).
Constraint == Check(clock, 1) /\ clock \in BOOLEAN

Tick == clock' = ~clock

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Liveness: the clock keeps flipping.
AlwaysEventuallyTrue == []<>(clock = TRUE)
AlwaysEventuallyFalse == []<>(clock = FALSE)

THEOREM Spec => []TypeOK
====
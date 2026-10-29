---------------------------- MODULE RecursiveClock ----------------------------
EXTENDS Naturals

VARIABLE clock

vars == << clock >>

\* Recursive operator: returns TRUE once the counter reaches 0,
\* checking along the way that b is a Boolean value.
RECURSIVE Check(_, _)
Check(b, n) ==
    IF n = 0
    THEN b \in BOOLEAN
    ELSE /\ b \in BOOLEAN
         /\ Check(b, n - 1)

\* Recursive operator: negates the Boolean b exactly n times.
RECURSIVE Flip(_, _)
Flip(b, n) ==
    IF n = 0
    THEN b
    ELSE ~Flip(b, n - 1)

\* Type predicate, expressed with the recursive operator Check.
TypeOK == Check(clock, 3)

\* Initial-state predicate. TLC reports coverage for the recursive call
\* to Flip that appears here. Because Init is evaluated only on initial
\* states, the recursive evaluations of Flip are counted once per initial
\* state, not once per distinct state reached.
Init == clock = Flip(FALSE, 2)

\* A separate state predicate, intended for use as a state constraint
\* (CONSTRAINT in the TLC configuration).
StateConstraint == Check(Flip(clock, 1), 2)

\* The only transition flips the Boolean value of clock.
Tick == clock' = Flip(clock, 1)

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: clock is always a Boolean.
THEOREM Spec => []TypeOK

\* Liveness: clock keeps alternating between both values.
AlwaysEventuallyTrue  == []<>(clock = TRUE)
AlwaysEventuallyFalse == []<>(clock = FALSE)

THEOREM Spec => AlwaysEventuallyTrue /\ AlwaysEventuallyFalse
=============================================================================
---- MODULE ClockBit ----
EXTENDS Naturals, FiniteSets

VARIABLE b

vars == << b >>

TypeOK == b \in BOOLEAN

Init == b \in BOOLEAN

Next == b' = ~b

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

ASSUME \A x \in BOOLEAN : ~(~x) = x

Constraint == ~(~b) = b

Successors == { v \in BOOLEAN : v = ~b }

Determinism == Cardinality(Successors) = 1

NoDeadlock == ENABLED Next

ToggleSafety == [][b' = ~b]_vars

TypeInvariance == []TypeOK

DeterminismInvariance == []Determinism

Progress == []NoDeadlock

Liveness == []<>(b = TRUE) /\ []<>(b = FALSE)

THEOREM Spec => TypeInvariance /\ DeterminismInvariance /\ Progress /\ ToggleSafety
====
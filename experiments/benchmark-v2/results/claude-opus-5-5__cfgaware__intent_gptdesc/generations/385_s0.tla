---------------------------- MODULE CounterMod ----------------------------
EXTENDS Naturals

CONSTANT C

ASSUME CAssump == C \in Nat \ {0}

VARIABLE x

vars == <<x>>

\* Type / range invariants
Inv  == x \in 0..C
Inv2 == x \in Nat /\ x <= C

\* Nondeterministic initialization choice within 0..C
InitND == x \in 0..C

\* Deterministic initial assertion of the range
InitDet == Inv

Init == InitND /\ InitDet

\* Atomic increment step modulo the bound
Incr == x' = (x + 1) % C

Next == Incr

\* Fairness for the single process
Fairness == WF_vars(Next)

Spec1 == Init /\ [][Next]_vars /\ Fairness

\* Safety: counter always stays within 0..C
Prop1 == []Inv

\* Liveness: value 0 recurs infinitely often
Prop2 == []<>(x = 0)

\* Fairness constraint stated as a property
Prop3 == WF_vars(Next)

\* Safety combined with recurrence
Prop4 == []Inv2 /\ []<>(x = 0)

\* Every step is an atomic modular increment
Prop5 == [][x' = (x + 1) % C]_vars

THEOREM Spec1 => Prop1 /\ Prop2 /\ Prop3 /\ Prop4 /\ Prop5
=============================================================================
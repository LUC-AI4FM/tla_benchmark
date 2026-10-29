---------------------------- MODULE CyclicCounter ----------------------------
EXTENDS Naturals

\* The cycle length. It is defined here rather than declared as a CONSTANT so
\* that the fixed configuration (which binds only x) needs no assignment.
\* Change this value to check other cycle lengths.
Modulus == 6

ASSUME Modulus \in Nat /\ Modulus > 0

VARIABLE x

vars == << x >>

\* Initial condition: the counter starts at zero.
Init == x = 0

\* Transition relation: advance the counter by one, modulo Modulus.
Increment == x' = (x + 1) % Modulus

Next == Increment

\* Weak fairness on Next ensures that steps keep being taken forever.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Safety properties

\* The counter is always a natural number.
TypeOK == x \in Nat

\* The counter always lies within 0 .. Modulus-1.
InRange == x \in 0 .. (Modulus - 1)

Inv == TypeOK /\ InRange

\* The step relation preserves the invariant: from any valid state,
\* every Next-step leads to another valid state.
StepPreservesInv == [][Inv /\ Next => Inv']_vars

THEOREM InitEstablishesInv == Init => Inv
THEOREM NextPreservesInv   == Inv /\ Next => Inv'
THEOREM SpecSafety         == Spec => []Inv

-----------------------------------------------------------------------------
\* Liveness: the system never deadlocks.

\* From every reachable valid state, a transition is always enabled.
NoDeadlock == [](ENABLED Next)

\* Under fairness, the counter keeps changing forever.
Progress == []<><< Next >>_vars

\* As a consequence, the counter returns to zero infinitely often.
ReturnsToZero == []<>(x = 0)

=============================================================================
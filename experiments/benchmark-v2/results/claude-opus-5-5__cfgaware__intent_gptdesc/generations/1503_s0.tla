---- MODULE SingleValueState ----
EXTENDS Integers, FiniteSets

VARIABLE x

vars == << x >>

(* The fixed finite universe of allowed integer values *)
Universe == 0..10

(* The numeric threshold used by the numeric predicate *)
Threshold == 3

(* The numeric predicate: the value must exceed the threshold *)
NumericPred(n) == n > Threshold

(* The additional Boolean requirement, which depends on the element *)
BoolCond(n) == (n % 2) = 0

(* A value is valid when it satisfies both constraints *)
Valid(n) == NumericPred(n) /\ BoolCond(n)

(* The set of values that are acceptable at initialization *)
ValidValues == { n \in Universe : Valid(n) }

(* The initialization predicate is satisfiable *)
ASSUME ValidValues # {}

(* Initialization nondeterministically picks any valid value *)
Init == \E n \in Universe : /\ NumericPred(n)
                            /\ BoolCond(n) = TRUE
                            /\ x = n

(* No transition changes the state: only stuttering steps happen *)
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(* Safety properties *)
TypeOK == x \in Universe

SafetyInv == /\ x \in Universe
             /\ NumericPred(x)
             /\ BoolCond(x)

InitSatisfiable == \E n \in Universe : Valid(n)

(* The value never changes after initialization *)
Persistence == \A v \in Universe : [](x = v => [](x = v))

(* Liveness is trivial: a valid value holds forever *)
AlwaysValid == []SafetyInv

THEOREM Spec => []SafetyInv
====
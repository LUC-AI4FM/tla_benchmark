---------------------------- MODULE TheoremRefs ----------------------------
EXTENDS Naturals

CONSTANT C

VARIABLE x

vars == <<x>>

ASSUME AssumeTrue == TRUE

ASSUME AssumeC == C = C

N == INSTANCE Naturals

Init == x = 0

Next == x' = IF x = 2 THEN 0 ELSE x + 1

Spec == Init /\ [][Next]_x

Spec1 == Init /\ [][Next]_x /\ WF_x(Next)

Inv == x \in 0..2

Inv2 == N!<=(x, 2) /\ N!>=(x, 0)

Prop1 == []Inv

Prop2 == []<>(x = 0)

Prop3 == <>(x = 2)

Prop4 == [](x = 1 => <>(x = 2))

Prop5 == [][x' # x]_x

THEOREM SafetyThm == Spec => []Inv

THEOREM Safety2Thm == Spec1 => []Inv2

THEOREM LiveThm == Spec1 => Prop2

THEOREM LeadsThm == Spec1 => Prop4

=============================================================================
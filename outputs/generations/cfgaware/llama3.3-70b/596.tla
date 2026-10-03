---------------------------- MODULE OneVariableTransitionSystem ----------------------------
EXTENDS Integers

CONSTANT None

VARIABLE x

Init == (x = 0)

Next == (x = 0) \/ (x' = 0 /\ x /= 0) \/ (x = 0 /\ (x' = 1 \/ x' = 2))

Spec == Init /\ [][Next]_x /\ WF_x(Next)

THEOREM Spec => <>[](x /= 1)
THEOREM Spec => <>[](x /= 2)
THEOREM Spec => []<>((x = 0) /\ (x' = 0))
THEOREM Spec => <>(x = 0)
THEOREM Spec => ~[]<>(x = 1)

Postcondition(trace) ==
  LET i == CHOOSE i \in DOMAIN trace : trace[i].x /= 0
  IN trace[i].x = 2

=============================================================================
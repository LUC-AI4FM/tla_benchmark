MODULE SmallSM
EXTENDS Naturals, Sets

CONSTANT Op

VARIABLE x

Init ==
  /\ x = 0

Next ==
  /\ x' \in Op(x)

Helper1(S) == S \subseteq Op(S)

Helper2(T) == T \subseteq UNION({ Op(t) : t ∈ T })

Spec == Init /\ [][Next]_x
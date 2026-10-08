MODULE SmallEven
EXTENDS Naturals, Integers

VARIABLE s

(* Predicate F: v is an integer in the range 0..9 and even *)
F(v) == v >= 0 /\ v <= 9 /\ Even(v)

Init == s = 0

Next == F(s')

Spec == Init /\ [] Next
MODULE SmallSystem
EXTENDS Integers

VARIABLE s

F(var) == var ∈ 0..9 /\ Mod(var,2)=0

Init == s = 0

Next == F(s')

Spec == Init /\ []Next
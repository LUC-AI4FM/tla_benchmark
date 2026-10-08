MODULE SmallSystem
EXTENDS TLC

VARIABLE x

DOMAIN == 1 .. 5

F(i) ==
  IF i = 1 THEN 2
  ELSE IF i = 2 THEN 3
  ELSE IF i = 3 THEN 4
  ELSE IF i = 4 THEN 5
  ELSE 1

N(1) == x' = F(x)
N(2) == x' = ((x Mod 5)+1)
N(3) == x' = 1

Stutter == x' = x

Init == x \in DOMAIN /\ x = 1

Next == (\E i \in 1 .. 3 : N(i)) \/ Stutter

Inv == \A i \in DOMAIN : (x = i -> F(i) = ((i Mod 5)+1))

Spec == Init /\ [] Next /\ [] Inv

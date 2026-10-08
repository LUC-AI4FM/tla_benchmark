MODULE TrivialStutter
EXTENDS Naturals

VARIABLES x, y

Init == /\ x = 0
      /\ y = 0
      /\ x = y

Next == /\ x' = x
        /\ y' = y

Spec == Init /\ [] Next
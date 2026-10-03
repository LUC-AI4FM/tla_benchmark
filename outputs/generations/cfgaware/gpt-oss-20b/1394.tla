```
------------------------------ MODULE x_unchanged ------------------------------
EXTENDS Naturals

VARIABLE x, y, z

Init == /\ x \in {1,2,3}
        /\ y \in {1,2,3}
        /\ z \in {1,2,3}

Next == /\ y' = y + 1
          /\ UNCHANGED <<x, z>>

Spec == Init /\ []Next

------------------------------ MODULE Github702 ------------------------------
EXTENDS Naturals

(* Constant‑valued operator fizzbuzz *)
fizzbuzz == 42

(* Instantiate x_unchanged, substituting the variable x with the constant expression fizzbuzz *)
INSTANCE x_unchanged WITH SUBSTITUTION x <- fizzbuzz
```
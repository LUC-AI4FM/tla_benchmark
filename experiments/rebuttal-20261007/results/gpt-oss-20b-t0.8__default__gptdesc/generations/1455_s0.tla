MODULE SubsetSpec
EXTENDS SETS, Naturals, Integers, Booleans

VARIABLE b

Init == 
  /\ b = TRUE

Next ==
  LET
      pos1 == Int \subseteq Int
      pos2 == Nat \subseteq Nat
      pos3 == Int \subseteq Nat
      neg1 == ~(1 .. 5 \subseteq {6,7})
      neg2 == ~({1,2} \subseteq 3 .. 4)
    IN
      b' = (pos1 /\ pos2 /\ pos3 /\ neg1 /\ neg2)

Inv ==
  /\ b = TRUE
  /\ b ∈ BOOLEAN

Spec == Init /\ []Next

END MODULE
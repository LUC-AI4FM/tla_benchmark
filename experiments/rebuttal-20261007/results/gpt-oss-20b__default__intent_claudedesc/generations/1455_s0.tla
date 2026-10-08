MODULE SubsetPowersetDemo

EXTENDS Naturals, Integers, FiniteSets

VARIABLES ok

(* --- Definitions of sets used in the test cases --- *)
smallRange == 1..3
largeRange == 1..5
range4      == 1..4
range3      == 1..3
A           == {1,2}
B           == {1,2,3}
emptySet    == {}
singleton   == {1}

(* --- Test cases for subset-of-powerset behavior --- *)
test1 == (SUBSET smallRange) \subseteq (SUBSET largeRange)
          /\ ~((SUBSET largeRange) \subseteq (SUBSET smallRange))

test2 == (SUBSET range3) \subseteq (SUBSET range4)
          /\ ~((SUBSET range4) \subseteq (SUBSET range3))

test3 == (SUBSET A) \subseteq (SUBSET B)

test4a == (SUBSET emptySet) \subseteq (SUBSET largeRange)
test4b == ~((SUBSET largeRange) \subseteq (SUBSET emptySet))
test4  == test4a /\ test4b

test5a == (SUBSET singleton) \subseteq (SUBSET INT)
test5b == ~((SUBSET INT) \subseteq (SUBSET singleton))
test5c == (SUBSET singleton) \subseteq (SUBSET NAT)
test5d == ~((SUBSET NAT) \subseteq (SUBSET singleton))
test5  == test5a /\ test5b /\ test5c /\ test5d

okVal == test1 /\ test2 /\ test3 /\ test4 /\ test5

(* --- Initial condition and next-state relation --- *)
Init == ok = okVal
Next == ok' = ok

Spec == Init /\ [][Next]_<<ok>>

(* --- Safety invariant --- *)
Inv == ok ∈ BOOLEAN /\ ok = TRUE

THEOREM Spec_Imply_Inv == Spec => []Inv

===============================================================================
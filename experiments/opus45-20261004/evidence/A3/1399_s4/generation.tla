---------------------------- MODULE BooleanToggle ----------------------------

VARIABLES x

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

(* State predicates about x *)
IsTrue == x = TRUE
IsFalse == x = FALSE

(* Type invariant *)
TypeOK == x \in BOOLEAN

=============================================================================
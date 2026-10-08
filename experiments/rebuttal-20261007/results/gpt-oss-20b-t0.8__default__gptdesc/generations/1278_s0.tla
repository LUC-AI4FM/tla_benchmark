MODULE EvenRangeSpec
EXTENDS Integers

VARIABLE s

(* Predicate that holds when its argument is an integer in the range 0..9 and is even *)
F(v) == (v \in 0 .. 9) /\ (v % 2 = 0)

(* Initial condition: s starts at 0 *)
Init == s = 0

(* Specification: initially s=0 and every step satisfies F(s') *)
Spec == Init /\ [] (F(s'))

=============================================================================
END MODULE EvenRangeSpec
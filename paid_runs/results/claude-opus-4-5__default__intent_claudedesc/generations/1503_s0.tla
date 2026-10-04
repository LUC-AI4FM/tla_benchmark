---------------------------- MODULE HigherOrderDemo ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS TRUE_CONST

VARIABLES x

--------------------------------------------------------------------------------
(* Higher-order operator that filters a set using both a unary and binary predicate *)
(* UnaryPred: element -> BOOLEAN *)
(* BinaryPred: (element, auxiliary) -> BOOLEAN *)
(* aux: auxiliary argument for the binary predicate *)
FilterSet(S, UnaryPred(_), BinaryPred(_, _), aux) ==
    {e \in S : UnaryPred(e) /\ BinaryPred(e, aux)}

--------------------------------------------------------------------------------
(* Concrete predicates to be passed as higher-order arguments *)

(* Unary predicate: element is greater than 1 *)
GreaterThanOne(e) == e > 1

(* Binary predicate: element is odd AND second argument is TRUE *)
OddAndTrue(e, b) == (e % 2 = 1) /\ b

--------------------------------------------------------------------------------
(* Apply the higher-order filter operator *)
(* Filters {1,2,3,4,5} for elements that are:
   - Greater than 1 (unary predicate)
   - Odd AND paired with TRUE (binary predicate)
   Result should be {3, 5} since:
   - 1 fails GreaterThanOne
   - 2 fails OddAndTrue (even)
   - 3 passes both (>1, odd, TRUE)
   - 4 fails OddAndTrue (even)
   - 5 passes both (>1, odd, TRUE)
*)
FilteredSet == FilterSet({1, 2, 3, 4, 5}, GreaterThanOne, OddAndTrue, TRUE)

--------------------------------------------------------------------------------
(* Initialization: x is drawn from the filtered set *)
Init == x \in FilteredSet

(* Next: system remains static, no state changes *)
Next == UNCHANGED x

(* Specification with stuttering *)
Spec == Init /\ [][Next]_x

--------------------------------------------------------------------------------
(* Type invariant to ensure x remains in expected domain *)
TypeInvariant == x \in {3, 5}

================================================================================
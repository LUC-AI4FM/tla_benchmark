---------------------------- MODULE InitDisjunction ----------------------------
(***************************************************************************)
(* A small TLC-oriented specification exploring how TLC generates initial *)
(* states from differently shaped disjunctive initial predicates over a    *)
(* single variable x.  The next-state relation is trivial (x never        *)
(* changes); the interest lies entirely in the structure of Init.          *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE x

vars == << x >>

(***************************************************************************)
(* Init1: A plain disjunction of two assignments with distinct values.     *)
(* TLC evaluates each disjunct separately and generates two distinct      *)
(* initial states: x = 1 and x = 2.  No duplicates are produced.           *)
(***************************************************************************)
Init1 == \/ x = 1
         \/ x = 2

(***************************************************************************)
(* Init2: Both disjuncts assign the same value.  TLC explores each         *)
(* disjunct independently and therefore generates the state x = 1 twice;  *)
(* the duplicate is detected by the fingerprint set, so only one distinct *)
(* initial state results, but two states are "generated".                  *)
(***************************************************************************)
Init2 == \/ x = 1
         \/ x = 1

(***************************************************************************)
(* Init3: The assignment comes first and the disjunction is a subsequent  *)
(* conjunct.  Once x is bound by "x \in {1, 2}", the disjunction is merely *)
(* evaluated as a boolean test, so each value of x is generated only       *)
(* once, even though both disjuncts may be true.  No duplicates.           *)
(***************************************************************************)
Init3 == /\ x \in {1, 2}
         /\ \/ x > 0
            \/ x < 3

(***************************************************************************)
(* Init4: Same conjuncts as Init3 but with the disjunction placed first.   *)
(* Now TLC splits on the disjunction before x is bound.  Each disjunct    *)
(* contains a test on an unbound variable, so TLC must treat the          *)
(* disjunction as a branching point; each branch then enumerates x, and  *)
(* values satisfying both disjuncts are generated twice (duplicates).     *)
(* Written with explicit assignment in each branch to remain evaluable.  *)
(***************************************************************************)
Init4 == \/ /\ x \in {1, 2}
            /\ x > 0
         \/ /\ x \in {1, 2}
            /\ x < 3

(***************************************************************************)
(* Init5: Disjunction pulled inside the set of values.  The assignment    *)
(* x \in S is performed once over the union, so each value is generated   *)
(* exactly once.  No duplicates.                                           *)
(***************************************************************************)
Init5 == x \in ({1} \cup {1, 2})

(***************************************************************************)
(* Init6: Double negation around a disjunction of assignments.  TLC       *)
(* cannot treat "x = 1" under a negation as an assignment, so wrapping    *)
(* the disjunction in ~~ prevents TLC from splitting it into branches.   *)
(* Here x is first bound by "x \in {1, 2}" and the double-negated         *)
(* disjunction is only evaluated as a test, so no duplicate states are   *)
(* generated, in contrast to Init2/Init4.                                   *)
(***************************************************************************)
Init6 == /\ x \in {1, 2}
         /\ ~~(\/ x = 1
               \/ x = 1
               \/ x = 2)

(***************************************************************************)
(* Init7: The same disjunction without double negation, placed first.     *)
(* TLC splits on it and the x = 1 branch is generated twice (duplicate). *)
(***************************************************************************)
Init7 == \/ x = 1
         \/ x = 1
         \/ x = 2

(***************************************************************************)
(* The initial predicate actually used by the specification.  Any of the *)
(* candidates above can be substituted here to observe TLC's behavior.    *)
(***************************************************************************)
Init == Init7

(***************************************************************************)
(* Trivial next-state relation: x never changes.                           *)
(***************************************************************************)
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* All candidate initial predicates describe subsets of {1, 2}.            *)
(***************************************************************************)
TypeOK == x \in {1, 2}

(* Since Next is a stuttering step, x keeps its initial value forever.    *)
Constancy == [][x' = x]_vars

THEOREM Spec => []TypeOK
=============================================================================
---- MODULE InitDisjunction ----
EXTENDS Naturals

VARIABLE x

vars == << x >>

(***************************************************************************)
(* Init1: A plain disjunction where both disjuncts assign the same value.  *)
(* TLC enumerates each disjunct separately, so it generates the state      *)
(* x = 1 twice; the duplicate is detected by the state fingerprint set and *)
(* only one distinct initial state results.                                *)
(***************************************************************************)
Init1 == \/ x = 1
         \/ x = 1

(***************************************************************************)
(* Init2: Conjunction with a disjunction placed *after* the assignment.    *)
(* x is already bound by the first conjunct, so the disjunction is only    *)
(* evaluated as a boolean test.  TLC should NOT generate a duplicate       *)
(* initial state here.                                                     *)
(***************************************************************************)
Init2 == /\ x = 1
         /\ \/ x = 1
            \/ x = 1

(***************************************************************************)
(* Init3: Conjunction with the disjunction placed *before* the test.       *)
(* The disjunction is reached while x is still unbound, so each disjunct   *)
(* acts as an assignment.  TLC SHOULD generate the state x = 1 twice       *)
(* (one per disjunct), though only one distinct state is kept.             *)
(***************************************************************************)
Init3 == /\ \/ x = 1
            \/ x = 1
         /\ x = 1

(***************************************************************************)
(* Init4: Double negation around the disjunction.  TLC does not look       *)
(* inside a negation to find assignments, so ~~(x = 1 \/ x = 1) is         *)
(* evaluated as a boolean only after x is bound by the first conjunct.     *)
(* TLC should NOT generate duplicate initial states.                       *)
(***************************************************************************)
Init4 == /\ x = 1
         /\ ~~(\/ x = 1
               \/ x = 1)

(***************************************************************************)
(* Init5: Disjunction with distinct values; generates two distinct initial *)
(* states, x = 1 and x = 2, with no duplicates.                            *)
(***************************************************************************)
Init5 == \/ x = 1
         \/ x = 2

(***************************************************************************)
(* Init6: Disjunction over a membership and an equality covering the same  *)
(* value.  TLC generates x = 1 from both disjuncts, so a duplicate         *)
(* initial state is produced (and collapsed into one distinct state).      *)
(***************************************************************************)
Init6 == \/ x \in {1, 2}
         \/ x = 1

(***************************************************************************)
(* The selected initial predicate used by Spec.                            *)
(***************************************************************************)
Init == Init3

(***************************************************************************)
(* Trivial next-state relation: x never changes.                           *)
(***************************************************************************)
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Simple sanity invariants.                                               *)
(***************************************************************************)
TypeOK == x \in {1, 2}

XIsOne == x = 1

====
---------------------------- MODULE InitDisjunction ----------------------------
(***************************************************************************)
(* A small TLC-oriented specification exploring how TLC generates initial  *)
(* states from different syntactic shapes of disjunctive initial           *)
(* predicates over a single variable x.                                    *)
(*                                                                         *)
(* TLC evaluates an initial predicate by walking its syntax tree: each     *)
(* disjunct is explored separately and each conjunct of the form           *)
(* x = e or x \in S that appears before x is assigned acts as an           *)
(* "assignment".  Depending on how the predicate is written, the same      *)
(* state may be produced along several branches (duplicates).  TLC         *)
(* discards duplicate states, but the number of generated states it        *)
(* reports can differ.                                                     *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x

vars == <<x>>

(***************************************************************************)
(* Init1: two disjuncts that each assign x the same value.  TLC explores   *)
(* both disjuncts and therefore SHOULD generate the state x = 1 twice      *)
(* (one duplicate).                                                        *)
(***************************************************************************)
Init1 == \/ x = 1
         \/ x = 1

(***************************************************************************)
(* Init2: the assignment comes first and the disjunction is placed AFTER   *)
(* it, as a constraint on an already-assigned variable.  Since x is        *)
(* assigned exactly once (x \in {1,2}) and the disjunction is merely       *)
(* evaluated as a boolean, TLC should NOT generate duplicate states:       *)
(* it generates x = 1 and x = 2 each exactly once.                         *)
(***************************************************************************)
Init2 == /\ x \in {1, 2}
         /\ \/ x = 1
            \/ x = 2

(***************************************************************************)
(* Init3: the same conjuncts as Init2 but in the opposite order.  Now the  *)
(* disjunction is evaluated while x is still unassigned, so each disjunct  *)
(* is an assignment.  Each branch yields a single state that is then       *)
(* checked against x \in {1,2}; no duplicates are generated here because   *)
(* the disjuncts assign different values.                                  *)
(***************************************************************************)
Init3 == /\ \/ x = 1
            \/ x = 2
         /\ x \in {1, 2}

(***************************************************************************)
(* Init4: the disjunction occurs before the assignment, but its disjuncts  *)
(* are overlapping constraints of the form x \in S.  Both disjuncts        *)
(* assign x = 2, so TLC SHOULD generate x = 2 twice (one duplicate).       *)
(***************************************************************************)
Init4 == /\ \/ x \in {1, 2}
            \/ x \in {2, 3}
         /\ x \in 1..3

(***************************************************************************)
(* Init5: the same overlapping disjunction as Init4 but placed after the   *)
(* assignment.  Because x is already assigned, the disjunction is only a   *)
(* boolean test and TLC should NOT generate duplicate states.              *)
(***************************************************************************)
Init5 == /\ x \in 1..3
         /\ \/ x \in {1, 2}
            \/ x \in {2, 3}

(***************************************************************************)
(* Init6: double negation of a disjunction.  TLC does not treat a negated  *)
(* formula as a source of assignments, so ~~(...) is evaluated as an       *)
(* opaque boolean constraint.  Hence the disjunction is NOT split into     *)
(* separate branches and TLC should NOT generate duplicate states, even    *)
(* though the disjuncts overlap.  (x must therefore be assigned first.)    *)
(***************************************************************************)
Init6 == /\ x \in 1..3
         /\ ~~(\/ x \in {1, 2}
               \/ x \in {2, 3})

(***************************************************************************)
(* Init7: an existential over a set whose elements yield the same state.   *)
(* Each witness i is a separate branch assigning x = 1, so TLC SHOULD      *)
(* generate the state x = 1 once per element (duplicates).                 *)
(***************************************************************************)
Init7 == \E i \in 1..3 : x = 1

(***************************************************************************)
(* The initial predicate used by the specification.  Any of the candidate  *)
(* predicates above may be substituted here; all of them describe          *)
(* (semantically) a nonempty set of initial states.                        *)
(***************************************************************************)
Init == Init4

(***************************************************************************)
(* The next-state relation is trivial: x never changes.                    *)
(***************************************************************************)
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Simple sanity invariants.                                               *)
(***************************************************************************)
TypeOK == x \in 1..3

(* The variable keeps its initial value forever. *)
Constant == [][x' = x]_vars

(* Semantic equivalences among the candidate initial predicates. *)
Init2EqualsInit3 == Init2 <=> Init3
Init4EqualsInit5 == Init4 <=> Init5
Init5EqualsInit6 == Init5 <=> Init6
Init1EqualsInit7 == Init1 <=> Init7

THEOREM Spec => []TypeOK
=============================================================================
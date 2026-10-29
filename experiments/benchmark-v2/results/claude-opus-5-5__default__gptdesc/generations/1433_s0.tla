---------------------------- MODULE InitDisjunction ----------------------------
(***************************************************************************)
(* A small TLC-oriented specification exploring how TLC generates initial *)
(* states from differently shaped disjunctive initial predicates over a    *)
(* single variable x.  The next-state relation is trivial (x never        *)
(* changes); the interest lies entirely in the structure of Init.         *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x

vars == << x >>

(***************************************************************************)
(* Init1: A plain disjunction of two assignments with distinct values.    *)
(* TLC splits the disjunction and generates two distinct initial states;  *)
(* no duplicates are generated.                                           *)
(***************************************************************************)
Init1 == \/ x = 1
         \/ x = 2

(***************************************************************************)
(* Init2: A disjunction whose disjuncts assign the SAME value.  TLC       *)
(* evaluates each disjunct separately and thus generates the state       *)
(* [x |-> 1] twice; the duplicate is detected and discarded by the       *)
(* fingerprint set, so only one distinct initial state results.          *)
(***************************************************************************)
Init2 == \/ x = 1
         \/ x = 1

(***************************************************************************)
(* Init3: Assignment precedes a disjunctive constraint.  Since x is bound *)
(* first, the subsequent disjunction is evaluated as a boolean test and   *)
(* is NOT split, so TLC generates exactly one initial state (no          *)
(* duplicates), even though both disjuncts are true.                     *)
(***************************************************************************)
Init3 == /\ x = 1
         /\ \/ x = 1
            \/ x \in {1}

(***************************************************************************)
(* Init4: The disjunction precedes the conjunct.  Here the disjunction is *)
(* the place where x gets assigned, so TLC splits it into two branches;  *)
(* both branches yield x = 1 and pass the subsequent test, so TLC        *)
(* generates the same initial state twice (a duplicate).                 *)
(***************************************************************************)
Init4 == /\ \/ x = 1
            \/ x \in {1}
         /\ x = 1

(***************************************************************************)
(* Init5: The disjunction is placed outside the conjunction.  Each       *)
(* disjunct independently assigns x, so TLC generates [x |-> 1] once per *)
(* disjunct, i.e., a duplicate initial state.                            *)
(***************************************************************************)
Init5 == \/ /\ x = 1
            /\ TRUE
         \/ /\ x = 1
            /\ x \in Nat

(***************************************************************************)
(* Init6: Double negation of a disjunction.  TLC does not push negations *)
(* through to recover the disjunctive structure for enumeration; the     *)
(* expression ~~(x = 1 \/ x = 1) cannot be used to assign x directly.     *)
(* Conjoining it after an assignment, it is evaluated as a plain boolean *)
(* test, so no duplicate states are generated.                           *)
(***************************************************************************)
Init6 == /\ x \in {1}
         /\ ~~(\/ x = 1
               \/ x = 1)

(***************************************************************************)
(* Init7: Double negation applied to the conjunct that follows a          *)
(* disjunctive assignment.  The disjunction still splits, producing the  *)
(* same state twice (a duplicate); the doubly negated test is merely a   *)
(* filter.                                                               *)
(***************************************************************************)
Init7 == /\ \/ x = 1
            \/ x = 1
         /\ ~~(x = 1)

(***************************************************************************)
(* The initial predicate actually used by the specification.  All        *)
(* candidates define the same set of initial states {[x |-> 1]} except   *)
(* Init1; Init is chosen to exercise the duplicate-generation case.      *)
(***************************************************************************)
Init == Init4

Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Sanity properties: the type of x, and that x never changes.           *)
(***************************************************************************)
TypeOK == x \in {1, 2}

Constant == [][x' = x]_vars

(***************************************************************************)
(* All the Init variants other than Init1 are semantically equivalent.   *)
(***************************************************************************)
InitsEquivalent == /\ Init2 <=> Init3
                   /\ Init3 <=> Init4
                   /\ Init4 <=> Init5
                   /\ Init5 <=> Init6
                   /\ Init6 <=> Init7

THEOREM Spec => []TypeOK
THEOREM Spec => Constant
=============================================================================
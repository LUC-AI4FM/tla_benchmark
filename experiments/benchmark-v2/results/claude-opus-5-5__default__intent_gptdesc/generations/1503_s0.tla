---------------------------- MODULE ConstantChoice ----------------------------
(***************************************************************************)
(* A single state variable x holds one value from a fixed finite set of    *)
(* integers.  Init picks, nondeterministically, any element that satisfies *)
(* a numeric predicate (greater than a threshold) and a Boolean condition  *)
(* associated with that element.  After that, no transition changes x.     *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    Universe,    \* the finite universe of allowed integer values
    Threshold,   \* the numeric threshold used by the numeric predicate
    Cond         \* Boolean requirement: a function Universe -> BOOLEAN

ASSUME UniverseIsFiniteIntSet ==
    /\ Universe \subseteq Int
    /\ IsFiniteSet(Universe)

ASSUME ThresholdIsInt == Threshold \in Int

ASSUME CondIsBoolFunction == Cond \in [Universe -> BOOLEAN]

(***************************************************************************)
(* The numeric predicate that filters acceptable integers.                 *)
(***************************************************************************)
NumPred(v) == v > Threshold

(***************************************************************************)
(* The additional Boolean requirement that must hold for the chosen value. *)
(***************************************************************************)
BoolReq(v) == Cond[v] = TRUE

(***************************************************************************)
(* The combined admissibility predicate and the set of admissible values.  *)
(***************************************************************************)
Admissible(v) == /\ v \in Universe
                 /\ NumPred(v)
                 /\ BoolReq(v)

AdmissibleSet == { v \in Universe : NumPred(v) /\ BoolReq(v) }

(***************************************************************************)
(* The initialization predicate is satisfiable.                            *)
(***************************************************************************)
ASSUME Satisfiable == \E v \in Universe : NumPred(v) /\ BoolReq(v)

VARIABLE x

vars == <<x>>

(***************************************************************************)
(* Initialization: nondeterministically choose some admissible value.      *)
(***************************************************************************)
Init == \E v \in Universe : /\ NumPred(v)
                            /\ BoolReq(v)
                            /\ x = v

(***************************************************************************)
(* No transition ever changes the state.                                   *)
(***************************************************************************)
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK == x \in Universe

Safety == /\ x \in Universe
          /\ NumPred(x)
          /\ BoolReq(x)

InAdmissibleSet == x \in AdmissibleSet

(* The value never changes across any step. *)
NeverChanges == [][x' = x]_vars

(***************************************************************************)
(* Liveness (trivial): once x holds a valid value, it holds it forever.    *)
(***************************************************************************)
Persistence == \A v \in Universe : [](x = v => [](x = v))

EventuallyAlwaysValid == <>[]Safety

-----------------------------------------------------------------------------
THEOREM SpecTypeOK          == Spec => []TypeOK
THEOREM SpecSafety          == Spec => []Safety
THEOREM SpecAdmissible      == Spec => []InAdmissibleSet
THEOREM SpecNeverChanges    == Spec => NeverChanges
THEOREM SpecPersistence     == Spec => Persistence
THEOREM SpecEventuallyValid == Spec => EventuallyAlwaysValid
=============================================================================
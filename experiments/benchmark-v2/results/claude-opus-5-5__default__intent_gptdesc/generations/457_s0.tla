---------------------------- MODULE DerivedFlag ----------------------------
EXTENDS Naturals

CONSTANTS Key, Val

ASSUME Key # Val \/ Key = Val   \* fixed mapping parameters (any values)

VARIABLES flag

vars == <<flag>>

-----------------------------------------------------------------------------
(* The fixed mapping contained in the derived collection when flag = TRUE *)
FixedMapping == [k |-> Key, v |-> Val]

(* Derived collection, computed deterministically from the current flag    *)
Derived == IF flag = TRUE THEN {FixedMapping} ELSE {}

(* Derived collection corresponding to flag = TRUE                         *)
TrueDerived == {FixedMapping}

-----------------------------------------------------------------------------
Init == flag = TRUE

(* The next flag value equals "is the derived collection empty?"           *)
Update == flag' = (Derived = {})

Next == Update

Stutter == UNCHANGED flag

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == flag \in BOOLEAN

(* Every non-stuttering transition satisfies the update relation *)
TransitionRule == [][flag' # flag => flag' = (Derived = {})]_vars

Safety == []TypeOK /\ TransitionRule

-----------------------------------------------------------------------------
(* "Possibility" property: from every reachable state it is always         *)
(* possible to take either a stuttering step or a consistent update step.  *)

CanStep == ENABLED (Stutter \/ Update)

AlwaysCanStep == []CanStep

-----------------------------------------------------------------------------
(* Invariance under stuttering-only behaviors starting with flag = TRUE    *)

StutterSpec == Init /\ [][Stutter]_vars

StutterInvariant == Derived = TrueDerived

StutterPreservesDerived == []StutterInvariant

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => TransitionRule
THEOREM Spec => AlwaysCanStep
THEOREM StutterSpec => StutterPreservesDerived

=============================================================================
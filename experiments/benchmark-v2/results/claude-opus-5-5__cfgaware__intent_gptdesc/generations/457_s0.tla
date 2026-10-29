---------------------------- MODULE BoolFlag ----------------------------
EXTENDS Naturals

VARIABLE flag

vars == <<flag>>

(* Derived collection, computed deterministically from the current flag.  *)
(* When flag is TRUE it holds a fixed mapping; otherwise it is empty.     *)
FixedMapping == {<<"key", 1>>}

Derived == IF flag = TRUE THEN FixedMapping ELSE {}

IsEmpty == Derived = {}

Init == flag = TRUE

(* Update: the next flag value equals "derived collection is empty". *)
Update == flag' = IsEmpty

Next == Update

Spec == Init /\ [][Next]_flag

-------------------------------------------------------------------------
(* Safety *)
TypeOK == flag \in BOOLEAN

TransitionOK == [][flag' = IsEmpty]_flag

Safety == []TypeOK /\ TransitionOK

(* Liveness-style possibility: in every reachable state a stuttering step *)
(* or a consistent update step is enabled.                              *)
StepPossible == ENABLED (Update \/ UNCHANGED flag)

AlwaysPossible == []StepPossible

(* Invariance: starting from flag = TRUE, stuttering steps preserve the *)
(* derived collection corresponding to TRUE.                            *)
StutterPreserves ==
    (flag = TRUE) => [][(UNCHANGED flag /\ Derived = FixedMapping) => (Derived' = FixedMapping)]_flag

StutterInvariant ==
    [][(flag = TRUE /\ UNCHANGED flag) => (Derived' = FixedMapping)]_vars

THEOREM Spec => Safety
THEOREM Spec => AlwaysPossible
THEOREM Spec => StutterInvariant
=========================================================================
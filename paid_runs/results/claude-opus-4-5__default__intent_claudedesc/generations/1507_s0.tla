---------------------------- MODULE Coverage ----------------------------
EXTENDS Booleans

VARIABLES clock

(* Recursive operator for initialization - demonstrates coverage tracking edge case *)
(* The recursive call appearing as an initializer may be skipped in coverage reporting *)
(* even though its parameters are evaluated *)
RECURSIVE InitRecursive(_)
InitRecursive(n) ==
    IF n = 0
    THEN TRUE
    ELSE InitRecursive(n - 1)

(* Recursive operator for state constraint *)
RECURSIVE ConstraintRecursive(_)
ConstraintRecursive(n) ==
    IF n = 0
    THEN TRUE
    ELSE ConstraintRecursive(n - 1)

(* Recursive operator for type checking *)
RECURSIVE TypeCheckRecursive(_, _)
TypeCheckRecursive(val, depth) ==
    IF depth = 0
    THEN val \in BOOLEAN
    ELSE TypeCheckRecursive(val, depth - 1)

(* State constraint using recursive operator *)
StateConstraint ==
    ConstraintRecursive(3)

(* Initial state uses recursive operator to determine initial value *)
Init ==
    /\ clock = InitRecursive(2)

(* Toggle the clock between TRUE and FALSE *)
Next ==
    /\ clock' = ~clock

(* Type invariant using recursive type checking operator *)
TypeOK ==
    TypeCheckRecursive(clock, 2)

(* Alternative direct type invariant for comparison *)
TypeInvariant ==
    clock \in BOOLEAN

(* The specification with weak fairness *)
Spec ==
    /\ Init
    /\ [][Next]_<<clock>>
    /\ WF_<<clock>>(Next)

(* Liveness property: the clock eventually toggles *)
Liveness ==
    /\ []<>(clock = TRUE)
    /\ []<>(clock = FALSE)

==========================================================================
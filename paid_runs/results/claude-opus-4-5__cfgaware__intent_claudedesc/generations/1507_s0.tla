---------------------------- MODULE specification ----------------------------

VARIABLES clock

(* Recursive operator for initialization - demonstrates TLC coverage edge case *)
RECURSIVE InitHelper(_)
InitHelper(n) ==
    IF n = 0
    THEN TRUE
    ELSE InitHelper(n - 1)

(* Recursive operator for state constraint *)
RECURSIVE ConstraintHelper(_)
ConstraintHelper(n) ==
    IF n = 0
    THEN TRUE
    ELSE ConstraintHelper(n - 1)

(* Recursive operator for type checking *)
RECURSIVE TypeCheckHelper(_, _)
TypeCheckHelper(val, depth) ==
    IF depth = 0
    THEN val \in BOOLEAN
    ELSE TypeCheckHelper(val, depth - 1)

(* Initial state - uses recursive operator *)
Init ==
    /\ InitHelper(3)
    /\ clock = TRUE

(* Next state - toggles the boolean clock *)
Next ==
    /\ ConstraintHelper(2)
    /\ clock' = ~clock

(* Type invariant using recursive checking *)
TypeOK ==
    TypeCheckHelper(clock, 2)

=============================================================================
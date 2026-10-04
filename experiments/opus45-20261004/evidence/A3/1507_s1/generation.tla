---- MODULE TinyClockSystem ----

EXTENDS Booleans

VARIABLES clock

(* Recursive operator that checks if a value is a Boolean *)
RECURSIVE Check(_)
Check(x) == IF x = TRUE THEN TRUE
            ELSE IF x = FALSE THEN TRUE
            ELSE FALSE

(* Recursive operator that flips a Boolean value *)
RECURSIVE Flip(_)
Flip(x) == IF x = TRUE THEN FALSE
           ELSE IF x = FALSE THEN TRUE
           ELSE x

(* Type predicate using the Check operator *)
TypeOK == Check(clock)

(* Constraint-like state predicate *)
ClockConstraint == clock \in BOOLEAN

(* Initial state predicate - clock starts as FALSE *)
(* Note: TLC coverage behavior for the recursive operator call Check(clock) *)
Init == /\ clock = FALSE
        /\ Check(clock)

(* Next state relation - flips the Boolean value of clock *)
Next == clock' = Flip(clock)

(* Specification with weak fairness on the Next action *)
Spec == Init /\ [][Next]_clock /\ WF_clock(Next)

(* Safety invariant: clock is always a Boolean *)
SafetyInvariant == TypeOK

(* Liveness property: clock eventually becomes TRUE *)
LivenessClockTrue == <>( clock = TRUE )

(* Liveness property: clock eventually becomes FALSE *)
LivenessClockFalse == <>( clock = FALSE )

(* Liveness property: clock always eventually flips *)
AlwaysFlips == [](clock = TRUE => <>(clock = FALSE)) /\ [](clock = FALSE => <>(clock = TRUE))

====
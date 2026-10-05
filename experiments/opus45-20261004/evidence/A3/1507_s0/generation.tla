---------------------------- MODULE TinyClockSystem ----------------------------
EXTENDS Booleans

VARIABLES clock

(* Recursive operator to check if a value is a Boolean *)
RECURSIVE Check(_)
Check(x) == IF x = TRUE THEN TRUE
            ELSE IF x = FALSE THEN TRUE
            ELSE FALSE

(* Recursive operator to flip a Boolean value *)
RECURSIVE Flip(_)
Flip(x) == IF x = TRUE THEN FALSE
           ELSE IF x = FALSE THEN TRUE
           ELSE x

(* Type invariant using the Check operator *)
TypeOK == Check(clock)

(* Initial state predicate - clock starts as FALSE *)
(* Note: The recursive operator call Check(clock) in Init may show *)
(* specific TLC coverage behavior during model checking *)
Init == clock = FALSE /\ Check(clock)

(* Constraint-like state predicate using Check *)
Constraint == Check(clock) = TRUE

(* Next state relation - flips the Boolean value of clock *)
Next == clock' = Flip(clock)

(* Specification with weak fairness on the Next action *)
Spec == Init /\ [][Next]_clock /\ WF_clock(Next)

(* Safety invariant: clock is always a Boolean *)
SafetyInvariant == clock \in BOOLEAN

(* Liveness property: clock eventually becomes TRUE *)
EventuallyTrue == <>(\E b \in BOOLEAN : clock = TRUE)

(* Liveness property: clock always eventually flips *)
AlwaysEventuallyFlips == [](clock = TRUE => <>(clock = FALSE)) /\ 
                         [](clock = FALSE => <>(clock = TRUE))

================================================================================
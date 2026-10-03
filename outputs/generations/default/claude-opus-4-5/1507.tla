---------------------------- MODULE TinyClockSystem ----------------------------
EXTENDS Booleans

VARIABLES clock

\* Recursive operator Check: returns TRUE if the argument is a Boolean
RECURSIVE Check(_)
Check(x) == IF x = TRUE THEN TRUE
            ELSE IF x = FALSE THEN TRUE
            ELSE FALSE

\* Recursive operator Flip: returns the negation of a Boolean
RECURSIVE Flip(_)
Flip(x) == IF x = TRUE THEN FALSE
           ELSE IF x = FALSE THEN TRUE
           ELSE x

\* Type invariant: clock must be a Boolean value
TypeOK == clock \in BOOLEAN

\* Type predicate using the recursive Check operator
TypePredicate == Check(clock)

\* Constraint-like state predicate (always satisfied for Boolean clock)
Constraint == Check(clock) = TRUE

\* Initial state predicate
\* Note: TLC coverage behavior for the recursive operator call Check(clock)
\* may show this call in Init coverage statistics
Init == /\ clock \in BOOLEAN
        /\ Check(clock)

\* Next state: flip the Boolean value of clock using the Flip operator
Next == clock' = Flip(clock)

\* Specification with weak fairness on Next
Spec == Init /\ [][Next]_clock /\ WF_clock(Next)

\* Safety invariant: clock is always a Boolean
SafetyInvariant == TypeOK

\* Liveness property: the clock eventually reaches TRUE
LivenessTrue == <>clock

\* Liveness property: the clock eventually reaches FALSE  
LivenessFalse == <>(~clock)

\* Liveness property: clock keeps changing (infinitely often TRUE and FALSE)
LivenessAlternation == /\ []<>clock
                       /\ []<>(~clock)

================================================================================
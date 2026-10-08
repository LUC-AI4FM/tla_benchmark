---------------------------- MODULE specification ----------------------------

EXTENDS Naturals

CONSTANT Limit

VARIABLE counter

\* Initial state predicate
Init == counter = 0

\* Increment action - only allowed when counter is strictly less than Limit
Increment == 
    /\ counter < Limit
    /\ counter' = counter + 1

\* Stuttering step - state remains unchanged
Stutter == 
    /\ UNCHANGED counter

\* Next state relation - either increment or stutter
Next == Increment \/ Stutter

\* Temporal specification with fairness to ensure liveness
Spec == Init /\ [][Next]_counter /\ WF_counter(Increment)

\* ============================================================================
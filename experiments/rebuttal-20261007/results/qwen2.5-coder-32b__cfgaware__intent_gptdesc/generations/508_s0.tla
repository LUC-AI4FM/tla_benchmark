------------------------------- MODULE SimpleProgram -------------------------------

VARIABLES x, terminated

CONSTANTS InitVal \* This constant is not strictly necessary but can be used to specify an initial value if needed

(*--algorithm SimpleProgram
variables x = 1, terminated = FALSE;

begin
    AssertSquare: 
        assert x * x <= 100;
        terminated := TRUE;
    
    while TRUE do
        await terminated;
    end while;
end algorithm;*)

\* State variables and their initial values
Init == /\ x \in 1..10
        /\ terminated = FALSE

\* Transition relation for the system
Next ==
    \/ /\ \neg terminated
       /\ x * x <= 100
       /\ terminated' = TRUE
       /\ x' = x
    \/ /\ terminated
       /\ terminated' = terminated
       /\ x' = x

\* Specification of the system behavior
Spec == Init /\ [][Next]_<<x, terminated>>

\* Safety property: The square of x is always at most 100
Safety == [](x * x <= 100)

\* Liveness property: The system eventually reaches a state where it is terminated
Termination == <>(terminated)

=============================================================================
------------------------------- MODULE FactorialCounter -------------------------------

CONSTANTS
    \* Constants for the factorial computations
    SMALL_CONSTANT,
    LARGE_CONSTANT

VARIABLES
    counter

ASSUME
    \* Ensure that the constants are positive integers
    CHOOSE SMALL_CONSTANT \in 1..8;
    CHOOSE LARGE_CONSTANT \in 9..20;

\* Define the factorial operator for any non-negative integer n
Factorial(n) == IF n = 0 THEN 1 ELSE n * Factorial(n - 1)

\* Initial predicate: counter starts at zero
Init == counter = 0

\* Next state relation: either a short update or a long update
Next ==
    \/ /\ counter' = Factorial(SMALL_CONSTANT)
       /\ UNCHANGED <<>>
    \/ /\ counter' = Factorial(LARGE_CONSTANT)
       /\ UNCHANGED <<>>

\* Specification of the system behavior
Spec ==
    Init /\ [][Next]_<<counter>>

\* Safety property: counter is always one of the factorial values
Safety == [](counter \in {Factorial(SMALL_CONSTANT), Factorial(LARGE_CONSTANT)})

\* Liveness property: there are infinitely many short updates and long updates
Liveness ==
    <>[]<>(counter' = Factorial(SMALL_CONSTANT)) /\
    <>[]<>(counter' = Factorial(LARGE_CONSTANT))

=============================================================================
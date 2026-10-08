---------------------------- MODULE GCDSubtraction ----------------------------

CONSTANTS 
    \* The first input, a fixed positive integer
    FIRST_INPUT,
    
    \* The domain of possible values for the second input
    SECOND_INPUT_DOMAIN

VARIABLES 
    \* The two numbers whose GCD is being computed
    x, y

ASSUME 
    \* FIRST_INPUT is a positive integer
    FIRST_INPUT \in Nat /\ FIRST_INPUT > 0,
    
    \* SECOND_INPUT_DOMAIN is a finite set of positive integers
    Finite(SECOND_INPUT_DOMAIN) /\ SECOND_INPUT_DOMAIN \subseteq Nat /\ SECOND_INPUT_DOMAIN /= {}

CONSTANT 
    \* The initial value for the second input, chosen nondeterministically from SECOND_INPUT_DOMAIN
    init_y

ASSUME 
    \* Ensure init_y is within the specified domain
    init_y \in SECOND_INPUT_DOMAIN

\* Define the greatest common divisor function using a recursive operator
RECURSIVE GCD(_, _)
GCD(a, b) == IF b = 0 THEN a ELSE GCD(b, a % b)

\* Initial predicate: sets x to FIRST_INPUT and y to init_y
Init == /\ x = FIRST_INPUT 
        /\ y = init_y

\* Next state relation: implements the subtraction-based Euclid algorithm
Next == \/ /\ x > y 
            /\ y > 0 
            /\ x' = x - y 
            /\ y' = y
         \/ /\ y > x 
            /\ x > 0 
            /\ x' = x 
            /\ y' = y - x
         \/ /\ (x = 0 \/ y = 0) 
            /\ x' = x 
            /\ y' = y

\* Specification: the behavior of the system is defined by Init and Next
Spec == Init /\ [][Next]_<<x, y>>

\* Invariant: GCD remains unchanged throughout execution
GcdInvariant == GCD(x, y) = GCD(FIRST_INPUT, init_y)

\* Safety property: both x and y are nonnegative integers and within a bounded range
Safety == /\ x \in 0..FIRST_INPUT 
          /\ y \in 0..FIRST_INPUT

\* Liveness property: the algorithm eventually terminates (one of x or y becomes zero)
Termination == <>[](x = 0 \/ y = 0)

=============================================================================
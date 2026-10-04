-------------------------------- MODULE GCD --------------------------------

EXTENDS Integers, Naturals

CONSTANTS MaxVal

ASSUME MaxVal \in Nat /\ MaxVal > 0

VARIABLES x, y, x0, y0, done

vars == <<x, y, x0, y0, done>>

\* Helper function to compute GCD for specification purposes
RECURSIVE GCDFunc(_, _)
GCDFunc(a, b) == IF b = 0 THEN a ELSE GCDFunc(b, a % b)

\* Initial state: x and y are positive integers in range, store original values
Init ==
    /\ x \in 1..MaxVal
    /\ y \in 1..MaxVal
    /\ x0 = x
    /\ y0 = y
    /\ done = FALSE

\* Subtract smaller from larger when x > y
SubtractXY ==
    /\ ~done
    /\ x > y
    /\ y > 0
    /\ x' = x - y
    /\ y' = y
    /\ x0' = x0
    /\ y0' = y0
    /\ done' = FALSE

\* Subtract smaller from larger when y > x
SubtractYX ==
    /\ ~done
    /\ y > x
    /\ x > 0
    /\ y' = y - x
    /\ x' = x
    /\ x0' = x0
    /\ y0' = y0
    /\ done' = FALSE

\* Swap values when needed (optional action for flexibility)
Swap ==
    /\ ~done
    /\ x < y
    /\ x' = y
    /\ y' = x
    /\ x0' = x0
    /\ y0' = y0
    /\ done' = FALSE

\* Termination: when x equals y, we have found the GCD
Terminate ==
    /\ ~done
    /\ x = y
    /\ done' = TRUE
    /\ x' = x
    /\ y' = y
    /\ x0' = x0
    /\ y0' = y0

\* Next state relation
Next == SubtractXY \/ SubtractYX \/ Terminate

\* Stuttering step when done
Stutter == done /\ UNCHANGED vars

\* Complete next state including stuttering
NextOrStutter == Next \/ Stutter

\* Fairness: ensure progress when actions are enabled
Fairness == WF_vars(Next)

\* Complete specification with fairness
Spec == Init /\ [][NextOrStutter]_vars /\ Fairness

\* ----- INVARIANTS -----

\* Both values remain positive integers throughout (before termination, both positive; after, at least result is positive)
PositiveInvariant ==
    /\ x \in Nat /\ x > 0
    /\ y \in Nat /\ y > 0

\* The GCD of the current pair equals the GCD of the original pair
GCDInvariant == GCDFunc(x, y) = GCDFunc(x0, y0)

\* Values stay within bounds
BoundedInvariant ==
    /\ x <= MaxVal
    /\ y <= MaxVal

\* Original values are preserved
OriginalPreserved ==
    /\ x0 \in 1..MaxVal
    /\ y0 \in 1..MaxVal

\* Type invariant combining all type constraints
TypeInvariant ==
    /\ x \in 1..MaxVal
    /\ y \in 1..MaxVal
    /\ x0 \in 1..MaxVal
    /\ y0 \in 1..MaxVal
    /\ done \in BOOLEAN

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ GCDInvariant

\* ----- CORRECTNESS PROPERTY -----

\* Upon termination, x (which equals y) is the GCD of the original values
CorrectnessOnTermination ==
    done => (x = GCDFunc(x0, y0) /\ x = y)

\* ----- LIVENESS PROPERTIES -----

\* The algorithm eventually terminates
EventuallyTerminates == <>(done)

\* Progress: if not done, eventually done
Progress == []( ~done => <>(done) )

\* Full liveness: termination with correct result
Liveness == <>(done /\ x = GCDFunc(x0, y0))

=============================================================================
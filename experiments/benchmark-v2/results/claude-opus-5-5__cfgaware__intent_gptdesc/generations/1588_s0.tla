------------------------------ MODULE EuclidGCD ------------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

(* A is the fixed positive input. *)
A == 12

ASSUME AAssumption == A \in Nat \ {0}

VARIABLES x, y, b

vars == <<x, y, b>>

Max(m, n) == IF m >= n THEN m ELSE n
Min(m, n) == IF m <= n THEN m ELSE n

Divides(d, n) == n % d = 0

CommonDivisors(m, n) == { d \in 1..Max(m, n) : Divides(d, m) /\ Divides(d, n) }

GCD(m, n) ==
    IF n = 0 THEN m
    ELSE IF m = 0 THEN n
    ELSE CHOOSE g \in CommonDivisors(m, n) :
            \A d \in CommonDivisors(m, n) : d <= g

Bound == Max(A, N)

-----------------------------------------------------------------------------
Init ==
    /\ b \in 1..N
    /\ x = A
    /\ y = b

Swap ==
    /\ y # 0
    /\ x < y
    /\ x' = y
    /\ y' = x
    /\ UNCHANGED b

Subtract ==
    /\ y # 0
    /\ ~(x < y)
    /\ x' = x - y
    /\ y' = y
    /\ UNCHANGED b

Step == Swap \/ Subtract

Done ==
    /\ y = 0
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
TypeOK ==
    /\ x \in 0..Bound
    /\ y \in 0..Bound
    /\ b \in 1..N

Safety ==
    /\ TypeOK
    /\ x + y > 0
    /\ (x = 0) => (y > 0)

GCDInvariant ==
    /\ CommonDivisors(x, y) = CommonDivisors(A, b)
    /\ GCD(x, y) = GCD(A, b)

Correctness == (y = 0) => (x = GCD(A, b))

Inv == Safety /\ GCDInvariant /\ Correctness

Termination == <>(y = 0)

=============================================================================
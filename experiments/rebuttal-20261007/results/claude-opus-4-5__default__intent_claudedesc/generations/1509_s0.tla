---------------------------- MODULE RecursiveDemo ----------------------------
EXTENDS Integers, Naturals

CONSTANTS N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLES state

-----------------------------------------------------------------------------
(* Recursive function computing factorial over domain 0..N *)
Factorial[n \in 0..N] ==
    IF n = 0 
    THEN 1
    ELSE n * Factorial[n-1]

(* Recursive function computing Fibonacci-like sequence over domain 0..N *)
Fib[n \in 0..N] ==
    IF n = 0 THEN 0
    ELSE IF n = 1 THEN 1
    ELSE Fib[n-1] + Fib[n-2]

(* Recursive function computing triangular numbers: T(n) = n + (n-1) + ... + 1 + 0 *)
Triangular[n \in 0..N] ==
    IF n = 0
    THEN 0
    ELSE n + Triangular[n-1]

(* The range of values produced by the Triangular function *)
TriangularRange == {Triangular[i] : i \in 0..N}

(* The range of values produced by the Factorial function *)
FactorialRange == {Factorial[i] : i \in 0..N}

(* The range of values produced by the Fibonacci function *)
FibRange == {Fib[i] : i \in 0..N}

-----------------------------------------------------------------------------
(* Initial state: state is set to a triangular number within the domain *)
Init == 
    state \in TriangularRange

(* Next state: the state never changes (stuttering only) *)
Next == 
    UNCHANGED state

(* Specification with stuttering tolerance *)
Spec == Init /\ [][Next]_state

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* Type invariant: state is a natural number *)
TypeInvariant == 
    state \in Nat

(* Main invariant: state is always a value in the range of the Triangular function *)
StateInTriangularRange == 
    state \in TriangularRange

(* Alternative invariant: there exists some n in the domain such that state equals Triangular[n] *)
StateIsTriangularNumber == 
    \E n \in 0..N : state = Triangular[n]

(* Combined safety property *)
SafetyInvariant == 
    /\ TypeInvariant
    /\ StateInTriangularRange
    /\ StateIsTriangularNumber

-----------------------------------------------------------------------------
(* Liveness property: the state is always stable *)
AlwaysStable == 
    []<>(state = state)

=============================================================================
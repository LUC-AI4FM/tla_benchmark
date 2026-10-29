------------------------------- MODULE EuclidGCD -------------------------------
(***************************************************************************)
(* Subtraction-based Euclidean algorithm for gcd(A, B), with A a fixed     *)
(* positive constant and B chosen nondeterministically from 1..N.          *)
(*                                                                         *)
(* State: the pair (x, y), plus b0, which records the initial B.           *)
(*   - Swap:     if x < y, exchange x and y.                               *)
(*   - Subtract: if y <= x and y # 0, set x to x - y.                      *)
(* The algorithm halts when y = 0. At that point x = gcd(A, b0).          *)
(* Division (%) is used only to define correctness, not in transitions.    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS A, N

ASSUME AssumeA == A \in Nat \ {0}
ASSUME AssumeN == N \in Nat \ {0}

VARIABLES x, y, b0

vars == <<x, y, b0>>

-----------------------------------------------------------------------------
(* Helper definitions; these are used only for specifying correctness.     *)

Max(m, n) == IF m >= n THEN m ELSE n

Bound == Max(A, N)

\* Set of common divisors of m and n. Requires m + n > 0.
CommonDivisors(m, n) ==
    { d \in 1..Max(m, n) : (m % d = 0) /\ (n % d = 0) }

\* Greatest element of the set of common divisors.
GCD(m, n) ==
    CHOOSE d \in CommonDivisors(m, n) :
        \A e \in CommonDivisors(m, n) : e <= d

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ b0 \in 1..N
    /\ x = A
    /\ y = b0

(* Transitions *)

Swap ==
    /\ x < y
    /\ x' = y
    /\ y' = x
    /\ UNCHANGED b0

Subtract ==
    /\ y # 0
    /\ y <= x
    /\ x' = x - y
    /\ UNCHANGED <<y, b0>>

Halted == y = 0

\* Stuttering in the halted state, so the spec does not deadlock.
Done ==
    /\ Halted
    /\ UNCHANGED vars

Step == Swap \/ Subtract

Next == Step \/ Done

\* Weak fairness on each loop step, so progress is never starved.
Fairness ==
    /\ WF_vars(Swap)
    /\ WF_vars(Subtract)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ b0 \in 1..N
    /\ x \in 0..Bound
    /\ y \in 0..Bound

\* Values stay within bounds: never above the initial inputs.
BoundsOK ==
    /\ x <= Max(A, b0)
    /\ y <= Max(A, b0)

\* Zeros appear only as the algorithm permits:
\*   - the pair is never (0, 0);
\*   - x is zero only transiently, with y positive and a Swap pending;
\*   - y is zero only in the halted state, with x positive.
NoUnexpectedZero ==
    /\ x + y > 0
    /\ (x = 0) => (y > 0)
    /\ (y = 0) => (x > 0)

\* Main invariant: the set of common divisors is preserved at every step.
CommonDivisorsInv ==
    CommonDivisors(x, y) = CommonDivisors(A, b0)

\* Consequence of the main invariant: the gcd is preserved.
GCDInv ==
    GCD(x, y) = GCD(A, b0)

\* Correctness at termination: when halted, x is the gcd.
Correctness ==
    Halted => (x = GCD(A, b0))

\* The initial input never changes.
B0Constant == [][b0' = b0]_vars

\* Once halted, the algorithm stays halted with the same result.
HaltedStable == [][Halted => (x' = x /\ y' = y)]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every behavior eventually halts with a zero component.
Termination == <>Halted

\* Every behavior eventually halts with the correct gcd.
EventuallyCorrect == <>(Halted /\ x = GCD(A, b0))

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ BoundsOK /\ NoUnexpectedZero
                   /\ CommonDivisorsInv /\ GCDInv /\ Correctness)
THEOREM Spec => Termination /\ EventuallyCorrect
=============================================================================
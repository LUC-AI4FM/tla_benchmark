------------------------------ MODULE EuclidGCD ------------------------------
(***************************************************************************)
(* The classical Euclidean algorithm for the GCD of two positive integers. *)
(*                                                                         *)
(* The pair (x, y) starts as two arbitrary positive integers in 1..N.      *)
(* Each step does one of two things:                                       *)
(*   - Swap: if x < y, exchange the two values.                            *)
(*   - Subtract: if x >= y, replace x by x - y.                            *)
(* The algorithm halts when x = 0. The remaining value y is then the GCD   *)
(* of the original pair.                                                   *)
(*                                                                         *)
(* x0 and y0 record the original inputs. They never change, so            *)
(* correctness can be stated against them.                                 *)
(*                                                                         *)
(* About positivity: the description also requires the run to end with     *)
(* one value at zero, so x cannot stay positive in the final state. The    *)
(* invariant therefore says y is always positive and x is positive in      *)
(* every non-halted state.                                                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N            \* Upper bound on the initial values (for model checking)

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y,       \* The current working pair
          x0, y0      \* The original inputs (never modified)

vars == <<x, y, x0, y0>>

-----------------------------------------------------------------------------
(* Mathematical definition of the GCD.                                     *)

Divides(d, n) == \E k \in 0..n : n = d * k

CommonDivisors(a, b) == { d \in 1..(a + b) : Divides(d, a) /\ Divides(d, b) }

GCD(a, b) == CHOOSE d \in CommonDivisors(a, b) :
                 \A e \in CommonDivisors(a, b) : e <= d

-----------------------------------------------------------------------------
(* Initial condition                                                       *)

Init == /\ x0 \in 1..N
        /\ y0 \in 1..N
        /\ x = x0
        /\ y = y0

(* Halting condition                                                       *)
Halted == x = 0

(* Algorithmic steps                                                       *)

Swap == /\ ~Halted
        /\ x < y
        /\ x' = y
        /\ y' = x
        /\ UNCHANGED <<x0, y0>>

Subtract == /\ ~Halted
            /\ x >= y
            /\ x' = x - y
            /\ y' = y
            /\ UNCHANGED <<x0, y0>>

Step == Swap \/ Subtract

(* After halting, the system stutters forever, so it never deadlocks.      *)
Terminate == /\ Halted
             /\ UNCHANGED vars

Next == Step \/ Terminate

(* Weak fairness on the algorithmic steps ensures progress.                *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety invariants                                                       *)

TypeOK == /\ x \in Nat
          /\ y \in Nat
          /\ x0 \in 1..N
          /\ y0 \in 1..N

(* y is always positive. x is positive until the halting state.            *)
PositiveInv == /\ y > 0
               /\ (~Halted) => (x > 0)

(* Both values stay within the initial bound.                              *)
BoundedInv == /\ x <= N
              /\ y <= N

(* The GCD of the working pair always equals the GCD of the inputs.        *)
GCDInvariant == GCD(x, y) = GCD(x0, y0)

(* Functional correctness: on termination, y is the GCD of the inputs.    *)
Correctness == Halted => (y = GCD(x0, y0))

(* Every Swap step preserves the GCD (action property).                    *)
SwapPreservesGCD == [][Swap => (GCD(x', y') = GCD(x, y))]_vars

(* Every Subtract step preserves the GCD (action property).                *)
SubtractPreservesGCD == [][Subtract => (GCD(x', y') = GCD(x, y))]_vars

(* The original inputs are never modified.                                 *)
InputsConstant == [][UNCHANGED <<x0, y0>>]_vars

(* Once halted, the algorithm stays halted with the same result.           *)
HaltIsFinal == [][Halted => UNCHANGED <<x, y>>]_vars

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)

(* Every behavior from every valid initial pair eventually halts.          *)
Termination == <>Halted

(* Eventually the algorithm halts with the correct GCD and stays there.    *)
EventuallyCorrect == <>[](Halted /\ y = GCD(x0, y0))

(* Progress: every non-halted state leads to a halted state.               *)
Progress == (~Halted) ~> Halted

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []PositiveInv
THEOREM Spec => []GCDInvariant
THEOREM Spec => []Correctness
THEOREM Spec => SwapPreservesGCD
THEOREM Spec => Termination
THEOREM Spec => EventuallyCorrect
=============================================================================
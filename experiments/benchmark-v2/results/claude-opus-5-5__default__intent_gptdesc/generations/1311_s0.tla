------------------------------- MODULE EuclidGCD -------------------------------
(***************************************************************************)
(* Subtraction-based Euclid algorithm for the GCD of two positive integers.*)
(* The first input is a fixed positive constant M. The second input is an  *)
(* arbitrary positive integer drawn from the finite range 1..N.            *)
(*                                                                         *)
(*   x := M ; y := y0 ;                                                    *)
(*   loop:  while y # 0 do                                                 *)
(*   test:     if x < y then swap(x, y) ;                                  *)
(*   sub:      x := x - y                                                  *)
(*          end ;                                                          *)
(*   done:  (* x = GCD(M, y0) *)                                           *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS M,   \* fixed positive first input
          N    \* upper bound of the range for the second input

ASSUME ConstAssump == /\ M \in Nat \ {0}
                      /\ N \in Nat \ {0}

VARIABLES x,   \* first component of the pair
          y,   \* second component of the pair
          y0,  \* the (nondeterministically chosen) initial second input
          pc   \* control location

vars == <<x, y, y0, pc>>

-----------------------------------------------------------------------------
(* Mathematical definitions *)

MaxOf(a, b) == IF a >= b THEN a ELSE b

Divisors(n) == {d \in 1..n : n % d = 0}

SetMax(S) == CHOOSE m \in S : \A s \in S : s <= m

\* GCD on naturals, with GCD(a, 0) = a and GCD(0, b) = b
GCD(a, b) == IF a = 0 THEN b
             ELSE IF b = 0 THEN a
             ELSE SetMax(Divisors(a) \cap Divisors(b))

Labels == {"loop", "test", "sub", "done"}

-----------------------------------------------------------------------------
(* Initial state *)

Init == /\ x = M
        /\ y \in 1..N
        /\ y0 = y
        /\ pc = "loop"

(* Loop guard: continue while y # 0, otherwise exit *)
Loop == /\ pc = "loop"
        /\ IF y # 0 THEN pc' = "test" ELSE pc' = "done"
        /\ UNCHANGED <<x, y, y0>>

(* Conditional swap so that x >= y before subtraction *)
Test == /\ pc = "test"
        /\ IF x < y
              THEN /\ x' = y
                   /\ y' = x
              ELSE UNCHANGED <<x, y>>
        /\ pc' = "sub"
        /\ UNCHANGED y0

(* Reduce the larger by the smaller *)
Sub == /\ pc = "sub"
       /\ x' = x - y
       /\ pc' = "loop"
       /\ UNCHANGED <<y, y0>>

(* Terminal state: algorithm has stopped (stuttering to avoid deadlock) *)
Terminated == /\ pc = "done"
              /\ UNCHANGED vars

Next == Loop \/ Test \/ Sub \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK == /\ x \in Nat
          /\ y \in Nat
          /\ y0 \in 1..N
          /\ pc \in Labels

NonNegative == x >= 0 /\ y >= 0

\* The pair stays within a range bounded by the initial values
Bounded == /\ x \in 0..MaxOf(M, y0)
           /\ y \in 0..MaxOf(M, y0)

\* GCD of the pair is preserved at every step
GCDPreserved == GCD(x, y) = GCD(M, y0)

\* Before subtraction, the larger value is in x
SwapCorrect == pc = "sub" => x >= y

\* On loop exit, the nonzero component equals the GCD
ExitCorrect == pc = "done" => (y = 0 /\ x # 0 /\ x = GCD(M, y0))

Safety == /\ TypeOK
          /\ NonNegative
          /\ Bounded
          /\ GCDPreserved
          /\ SwapCorrect
          /\ ExitCorrect

THEOREM Spec => []Safety

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Termination is always reached
Termination == <>(pc = "done")

\* Once terminated, the algorithm stays terminated with the correct result
StaysDone == [](pc = "done" => [](pc = "done" /\ x = GCD(M, y0)))

THEOREM Spec => Termination /\ StaysDone
=============================================================================
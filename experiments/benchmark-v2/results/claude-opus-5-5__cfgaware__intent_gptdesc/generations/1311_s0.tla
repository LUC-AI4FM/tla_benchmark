---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Integers, Naturals

(***************************************************************************)
(* Subtraction-based Euclid algorithm, modeled as a sequential program     *)
(* with explicit control flow:                                              *)
(*                                                                          *)
(*   x := M ; y :\in 1..N ;                                                 *)
(*   Loop:  while y # 0 do                                                  *)
(*   Swap:     if x < y then (x, y) := (y, x) ;                             *)
(*   Sub:      x := x - y                                                   *)
(*          end while ;                                                     *)
(*   Done:                                                                  *)
(*                                                                          *)
(* On exit y = 0 and x = GCD(M, y0).                                        *)
(***************************************************************************)

M == 12           \* fixed positive first input
N == 10           \* second input ranges over 1..N

ASSUME M \in Nat \ {0} /\ N \in Nat \ {0}

VARIABLES x, y, pc, y0

vars == <<x, y, pc, y0>>

Max(a, b) == IF a >= b THEN a ELSE b

Divides(p, n) == \E q \in 0..n : n = p * q

GCD(a, b) ==
    CHOOSE d \in 1..Max(a, b) :
        /\ Divides(d, a)
        /\ Divides(d, b)
        /\ \A e \in 1..Max(a, b) : (Divides(e, a) /\ Divides(e, b)) => e <= d

Bound == Max(M, N)

---------------------------------------------------------------------------

Init ==
    /\ x = M
    /\ y \in 1..N
    /\ y0 = y
    /\ pc = "Loop"

LoopTest ==
    /\ pc = "Loop"
    /\ IF y # 0
          THEN pc' = "Swap"
          ELSE pc' = "Done"
    /\ UNCHANGED <<x, y, y0>>

SwapStep ==
    /\ pc = "Swap"
    /\ IF x < y
          THEN /\ x' = y
               /\ y' = x
          ELSE UNCHANGED <<x, y>>
    /\ pc' = "Sub"
    /\ UNCHANGED y0

SubStep ==
    /\ pc = "Sub"
    /\ x' = x - y
    /\ pc' = "Loop"
    /\ UNCHANGED <<y, y0>>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == LoopTest \/ SwapStep \/ SubStep \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopTest \/ SwapStep \/ SubStep)

---------------------------------------------------------------------------
(* Invariants and properties *)

TypeOK ==
    /\ x \in Nat
    /\ y \in Nat
    /\ y0 \in 1..N
    /\ pc \in {"Loop", "Swap", "Sub", "Done"}

GCDPreserved ==
    (x + y > 0) /\ GCD(x, y) = GCD(M, y0)

\* Before subtraction the larger value is in x
SwapCorrect == (pc = "Sub") => (x >= y /\ y > 0)

CorrectAtExit ==
    (pc = "Done") => (y = 0 /\ x = GCD(M, y0))

Safety ==
    /\ x >= 0
    /\ y >= 0
    /\ x <= Max(M, y0)
    /\ y <= Max(M, y0)
    /\ x <= Bound
    /\ y <= Bound

Inv == TypeOK /\ GCDPreserved /\ SwapCorrect /\ CorrectAtExit /\ Safety

Termination == <>(pc = "Done")

THEOREM Spec => []Inv
THEOREM Spec => Termination
=============================================================================
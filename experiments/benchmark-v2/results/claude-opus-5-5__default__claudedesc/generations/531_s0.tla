---------------------------- MODULE MCSession3proj ----------------------------
(***************************************************************************)
(* Model-checking module for Session3proj.                                 *)
(*                                                                         *)
(* The original Session3proj base module was not provided. To keep this   *)
(* module self-contained and parsable by SANY, it includes a stand-in      *)
(* base specification. The stand-in is a division algorithm that works by *)
(* repeated subtraction and divides n \in NSet by a non-zero m \in MSet.   *)
(* MSet excludes zero, so the division is always well defined.             *)
(*                                                                         *)
(* Accompanying TLC configuration (MCSession3proj.cfg):                    *)
(*   SPECIFICATION Spec                                                    *)
(*   CONSTANTS                                                             *)
(*     MSet <- ConstMSet                                                   *)
(*     NSet <- ConstNSet                                                   *)
(*   INVARIANTS TypeOK DivInvariant Correctness                            *)
(*   PROPERTIES Termination                                                *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS MSet, NSet

\* Concrete finite values used for model checking
ConstMSet == (-8..-1) \cup (1..8)   \* non-zero integers in -8..8
ConstNSet == 0..10                   \* natural numbers 0..10

ASSUME MSet \subseteq (Int \ {0})
ASSUME NSet \subseteq Nat

VARIABLES m, n, q, r, done

vars == <<m, n, q, r, done>>

Abs(x) == IF x < 0 THEN -x ELSE x

-----------------------------------------------------------------------------
Init == /\ m \in MSet
        /\ n \in NSet
        /\ q = 0
        /\ r = n
        /\ done = FALSE

\* Subtract |m| from the remainder while it is still at least |m|
Step == /\ ~done
        /\ r >= Abs(m)
        /\ r' = r - Abs(m)
        /\ q' = q + 1
        /\ UNCHANGED <<m, n, done>>

\* The remainder is smaller than |m|, so the computation is finished
Finish == /\ ~done
          /\ r < Abs(m)
          /\ done' = TRUE
          /\ UNCHANGED <<m, n, q, r>>

\* Stuttering after termination, which avoids deadlock
Terminated == /\ done
              /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

-----------------------------------------------------------------------------
\* Safety properties

TypeOK == /\ m \in MSet
          /\ n \in NSet
          /\ q \in Nat
          /\ r \in Nat
          /\ done \in BOOLEAN

\* Loop invariant of the division algorithm
DivInvariant == /\ n = q * Abs(m) + r
                /\ r >= 0

\* Signed quotient, which accounts for a negative divisor
Quotient == IF m < 0 THEN -q ELSE q

\* On termination, n = Quotient * m + r with 0 <= r < |m|
Correctness == done => /\ n = Quotient * m + r
                       /\ 0 <= r
                       /\ r < Abs(m)

-----------------------------------------------------------------------------
\* Liveness property: the computation always terminates

Termination == <>done

THEOREM Spec => [](TypeOK /\ DivInvariant /\ Correctness)
THEOREM Spec => Termination
=============================================================================
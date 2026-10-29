------------------------------- MODULE MC -------------------------------
EXTENDS Integers, TLC

(***************************************************************************)
(* Constants of the base specification (Session3proj).                     *)
(***************************************************************************)
CONSTANTS MSet, NSet

(***************************************************************************)
(* Concrete finite values used for model checking.                         *)
(***************************************************************************)
ConstMSet == (-8..-1) \cup (1..8)
ConstNSet == 0..10

(***************************************************************************)
(* Behavioral specification: for a non-zero m chosen from MSet and a       *)
(* natural number n chosen from NSet, compute the quotient and remainder   *)
(* of n divided by |m| by repeated subtraction. A zero value of m would    *)
(* make the loop never terminate, which is why MSet excludes zero.         *)
(***************************************************************************)
VARIABLES m, n, q, r, done

vars == <<m, n, q, r, done>>

Abs(x) == IF x < 0 THEN -x ELSE x

TypeOK ==
    /\ m \in MSet
    /\ n \in NSet
    /\ q \in Nat
    /\ r \in Int
    /\ done \in BOOLEAN

Init ==
    /\ m \in MSet
    /\ n \in NSet
    /\ q = 0
    /\ r = n
    /\ done = FALSE

Subtract ==
    /\ ~done
    /\ r >= Abs(m)
    /\ r' = r - Abs(m)
    /\ q' = q + 1
    /\ UNCHANGED <<m, n, done>>

Finish ==
    /\ ~done
    /\ r < Abs(m)
    /\ done' = TRUE
    /\ UNCHANGED <<m, n, q, r>>

Terminated ==
    /\ done
    /\ UNCHANGED vars

Next == Subtract \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Subtract \/ Finish)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
DivInvariant == n = q * Abs(m) + r

RemainderNonNeg == r >= 0

Correct == done => (0 <= r /\ r < Abs(m) /\ q = n \div Abs(m))

Termination == <>done

=============================================================================
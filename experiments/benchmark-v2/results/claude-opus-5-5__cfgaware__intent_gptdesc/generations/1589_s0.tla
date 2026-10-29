---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Bound on the initial values, used for model checking.                   *)
(***************************************************************************)
MaxVal == 6

VARIABLES x, y, x0, y0, pc, lastAct, steps

vars == <<x, y, x0, y0, pc, lastAct, steps>>

(***************************************************************************)
(* Mathematical definition of the GCD.                                     *)
(***************************************************************************)
Divides(d, n) == \E k \in 0..n : n = d * k

MaxOf(a, b) == IF a >= b THEN a ELSE b

GCD(a, b) ==
  IF b = 0 THEN a
  ELSE IF a = 0 THEN b
  ELSE CHOOSE d \in 1..MaxOf(a, b) :
         /\ Divides(d, a)
         /\ Divides(d, b)
         /\ \A e \in 1..MaxOf(a, b) :
               (Divides(e, a) /\ Divides(e, b)) => e <= d

StepBound == 2 * (2 * MaxVal) + 2

TypeOK ==
  /\ x \in 0..MaxVal
  /\ y \in 0..MaxVal
  /\ x0 \in 1..MaxVal
  /\ y0 \in 1..MaxVal
  /\ pc \in {"Loop", "Done"}
  /\ lastAct \in {"none", "swap", "sub", "halt"}
  /\ steps \in Nat

(***************************************************************************)
(* Initial condition.                                                      *)
(***************************************************************************)
Init ==
  /\ x0 \in 1..MaxVal
  /\ y0 \in 1..MaxVal
  /\ x = x0
  /\ y = y0
  /\ pc = "Loop"
  /\ lastAct = "none"
  /\ steps = 0

(***************************************************************************)
(* Algorithm steps.                                                        *)
(***************************************************************************)
Swap ==
  /\ pc = "Loop"
  /\ y # 0
  /\ x < y
  /\ x' = y
  /\ y' = x
  /\ lastAct' = "swap"
  /\ steps' = steps + 1
  /\ UNCHANGED <<x0, y0, pc>>

Reduce ==
  /\ pc = "Loop"
  /\ y # 0
  /\ x >= y
  /\ x' = x - y
  /\ lastAct' = "sub"
  /\ steps' = steps + 1
  /\ UNCHANGED <<y, x0, y0, pc>>

Halt ==
  /\ pc = "Loop"
  /\ y = 0
  /\ pc' = "Done"
  /\ lastAct' = "halt"
  /\ UNCHANGED <<x, y, x0, y0, steps>>

Terminated ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Swap \/ Reduce \/ Halt \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Swap \/ Reduce \/ Halt)

(***************************************************************************)
(* State predicates.                                                       *)
(***************************************************************************)
Finished == pc = "Done"

SwapOccurs == lastAct = "swap"

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
Invariant ==
  /\ TypeOK
  /\ x + y > 0
  /\ (pc = "Loop" /\ lastAct = "none") => (x > 0 /\ y > 0)
  /\ GCD(x, y) = GCD(x0, y0)
  /\ SwapOccurs => (x > y /\ GCD(x, y) = GCD(x0, y0))
  /\ Finished => (y = 0 /\ x = GCD(x0, y0))

PossibleCounts == steps \in 0..StepBound

_POSSIBLE == Finished \/ ENABLED (Swap \/ Reduce \/ Halt)

(***************************************************************************)
(* Liveness: the algorithm eventually terminates.                          *)
(***************************************************************************)
Termination == <>Finished

Correctness == [](Finished => x = GCD(x0, y0))

=============================================================================
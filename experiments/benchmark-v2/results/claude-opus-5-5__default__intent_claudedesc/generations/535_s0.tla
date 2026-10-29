---------------------------- MODULE MCTupleMax ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Model-checking configuration for a tuple-processing system that        *)
(* computes the maximum element of a finite tuple of integers.             *)
(* Concrete values replace the abstract constants:                         *)
(*   - MCMinusInfinity : a large negative sentinel ("negative infinity")   *)
(*   - MCInput         : a small test tuple of integers                    *)
(***************************************************************************)

MCMinusInfinity == -1000000

MCInput == <<3, 1, 4, 1, 5>>

MinusInfinity == MCMinusInfinity
Input         == MCInput

ASSUME /\ MinusInfinity \in Int
       /\ Input \in Seq(Int)
       /\ \A k \in 1..Len(Input) : Input[k] > MinusInfinity

-----------------------------------------------------------------------------

VARIABLES max, i

vars == <<max, i>>

Range(s) == {s[k] : k \in 1..Len(s)}

SetMax(S) == IF S = {} THEN MinusInfinity
             ELSE CHOOSE x \in S : \A y \in S : y <= x

Prefix(n) == [k \in 1..n |-> Input[k]]

Init == /\ max = MinusInfinity
        /\ i = 1

Step == /\ i <= Len(Input)
        /\ max' = IF Input[i] > max THEN Input[i] ELSE max
        /\ i' = i + 1

Done == /\ i > Len(Input)
        /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ max \in Int
          /\ i \in 1..(Len(Input) + 1)

SentinelBound == max >= MinusInfinity

LoopInvariant == max = SetMax(Range(Prefix(i - 1)))

Correctness == (i > Len(Input)) =>
                 /\ max = SetMax(Range(Input))
                 /\ (Len(Input) > 0 => max \in Range(Input))
                 /\ \A k \in 1..Len(Input) : Input[k] <= max

(* Liveness properties *)

Termination == <>(i > Len(Input))

EventuallyCorrect == <>[](max = SetMax(Range(Input)))

=============================================================================
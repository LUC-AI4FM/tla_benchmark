---------------------------- MODULE MCMaxTuples ----------------------------
(***************************************************************************)
(* Model-checking configuration module.  It declares the constants of a   *)
(* base algorithm that computes the maximum element of a tuple, together  *)
(* with finite concrete values for those constants:                       *)
(*                                                                         *)
(*   - minValue : sentinel standing for "negative infinity", i.e. the     *)
(*                maximum of the empty tuple.                              *)
(*   - Tuples   : the set of input tuples the algorithm may receive.      *)
(*                                                                         *)
(* The configuration substitutes minValue <- ConstMinValue and            *)
(* Tuples <- ConstTuples so that TLC explores a finite state space.        *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

CONSTANTS minValue, Tuples

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete finite instantiations of the constants.                        *)
(***************************************************************************)

\* Sentinel value smaller than every element that can appear in a tuple.
ConstMinValue == -1

\* Tuples of length 0..3, where a tuple of length n has elements in 0..n.
\* The empty tuple << >> is included (n = 0).
ConstTuples == UNION { [1..n -> 0..n] : n \in 0..3 }

-----------------------------------------------------------------------------
(***************************************************************************)
(* Base algorithm: sequentially compute the maximum of an input tuple.    *)
(***************************************************************************)

ASSUME minValue \in Int

VARIABLES inp, result, i

vars == <<inp, result, i>>

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

MaxOf(t) == IF Len(t) = 0 THEN minValue
            ELSE Max({t[k] : k \in 1..Len(t)})

TypeOK ==
    /\ inp \in Tuples
    /\ i \in 1..(Len(inp) + 1)
    /\ result \in Int

Init ==
    /\ inp \in Tuples
    /\ result = minValue
    /\ i = 1

Step ==
    /\ i <= Len(inp)
    /\ result' = IF inp[i] > result THEN inp[i] ELSE result
    /\ i' = i + 1
    /\ UNCHANGED inp

Done ==
    /\ i > Len(inp)
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties to check.                                                    *)
(***************************************************************************)

\* The partial result is always the maximum of the prefix processed so far.
PartialCorrect ==
    result = IF i = 1 THEN minValue
             ELSE Max({inp[k] : k \in 1..(i - 1)})

\* When the algorithm has finished, result is the maximum of the tuple.
Correct == (i > Len(inp)) => (result = MaxOf(inp))

\* The result never drops below the sentinel.
BoundedBelow == result >= minValue

\* The algorithm eventually terminates.
Termination == <>(i > Len(inp))

=============================================================================
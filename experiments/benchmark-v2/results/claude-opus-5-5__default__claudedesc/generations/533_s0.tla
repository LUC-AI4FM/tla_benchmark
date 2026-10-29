---------------------------- MODULE MC_Session4 ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the "Session4" specification.               *)
(*                                                                         *)
(* The original wrapper EXTENDS Session4 and defines two constants:        *)
(*   ConstMinValue == -99999                                               *)
(*   ConstTuples   == UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }        *)
(*                                                                         *)
(* The TLC configuration file is:                                          *)
(*   SPECIFICATION Spec                                                    *)
(*   CONSTANTS minValue <- ConstMinValue                                   *)
(*             Tuples   <- ConstTuples                                     *)
(*                                                                         *)
(* Session4 is not available, so this module is self-contained so that     *)
(* SANY can parse it. The behavior below is an assumed reconstruction,     *)
(* not the real Session4. It supposes Session4 scans a tuple drawn from    *)
(* Tuples and computes its maximum, starting from minValue.                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS minValue, Tuples

ASSUME minValue \in Int

VARIABLES tup, i, max

vars == <<tup, i, max>>

(***************************************************************************)
(* Concrete constant definitions, as given by the wrapper.                 *)
(***************************************************************************)
ConstMinValue == -99999

ConstTuples == UNION { [1..l -> (l+1)..(2*l)] : l \in 0..5 }

(***************************************************************************)
(* Assumed Session4 behavior: scan a tuple and compute its maximum.        *)
(***************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

Range(t) == { t[k] : k \in 1..Len(t) }

Init == /\ tup \in Tuples
        /\ i = 1
        /\ max = minValue

Step == /\ i <= Len(tup)
        /\ max' = IF tup[i] > max THEN tup[i] ELSE max
        /\ i' = i + 1
        /\ UNCHANGED tup

Done == /\ i > Len(tup)
        /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK == /\ tup \in Tuples
          /\ i \in 1..(Len(tup) + 1)
          /\ max \in Int

PartialCorrect ==
    max = IF i = 1 THEN minValue
          ELSE Max(Range(SubSeq(tup, 1, i - 1)) \cup {minValue})

Correct ==
    (i > Len(tup)) =>
        (max = IF Len(tup) = 0 THEN minValue ELSE Max(Range(tup)))

(***************************************************************************)
(* Liveness property                                                       *)
(***************************************************************************)
Termination == <>(i > Len(tup))

=============================================================================
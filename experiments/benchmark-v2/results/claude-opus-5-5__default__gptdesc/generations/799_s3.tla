---------------------------- MODULE MCFindHighest ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the FindHighest algorithm.                   *)
(*                                                                         *)
(* The original FindHighest spec draws f from Seq(Nat), which is infinite. *)
(* This module bounds the model with two constants:                        *)
(*   - MaxLength : the maximum length of the input sequence f              *)
(*   - MaxNat    : naturals are restricted to the range 0..MaxNat          *)
(*                                                                         *)
(* The FindHighest algorithm is written out here so that the module parses *)
(* on its own, with its input domain replaced by the bounded set.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS MaxLength, MaxNat

ASSUME MaxLengthAssumption == MaxLength \in Nat
ASSUME MaxNatAssumption    == MaxNat \in Nat

---------------------------------------------------------------------------
(***************************************************************************)
(* Model helper operators                                                  *)
(***************************************************************************)

\* Bounded replacement for Nat
BoundedNat == 0..MaxNat

\* All sequences over S of length at most MaxLength
SeqOf(S) == UNION { [1..n -> S] : n \in 0..MaxLength }

\* Bounded replacement for Seq(Nat)
BoundedSeqNat == SeqOf(BoundedNat)

---------------------------------------------------------------------------
(***************************************************************************)
(* FindHighest algorithm, with its input domain bounded                    *)
(***************************************************************************)

VARIABLES f, h, i, pc

vars == << f, h, i, pc >>

max(a, b) == IF a >= b THEN a ELSE b

Init ==
    /\ f \in BoundedSeqNat
    /\ h = -1
    /\ i = 1
    /\ pc = "lb"

lb ==
    /\ pc = "lb"
    /\ IF i <= Len(f)
         THEN /\ h' = max(h, f[i])
              /\ i' = i + 1
              /\ pc' = "lb"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED << h, i >>
    /\ UNCHANGED f

\* Stuttering step after termination, which prevents deadlock
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == lb \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(lb)

---------------------------------------------------------------------------
(***************************************************************************)
(* Model constraint: bound the length of f and the range of naturals       *)
(***************************************************************************)

StateConstraint ==
    /\ Len(f) <= MaxLength
    /\ \A j \in 1..Len(f) : f[j] \in BoundedNat

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

TypeOK ==
    /\ f \in BoundedSeqNat
    /\ h \in BoundedNat \cup {-1}
    /\ i \in 1..(Len(f) + 1)
    /\ pc \in {"lb", "Done"}

\* Loop invariant: h is the maximum of the prefix already scanned
LoopInvariant ==
    /\ \A j \in 1..(i - 1) : f[j] <= h
    /\ (i = 1) <=> (h = -1)
    /\ (i > 1) => \E j \in 1..(i - 1) : f[j] = h

\* Correctness: on termination h is the highest element of f
Correctness ==
    pc = "Done" =>
        /\ \A j \in 1..Len(f) : f[j] <= h
        /\ (Len(f) > 0) => \E j \in 1..Len(f) : f[j] = h
        /\ (Len(f) = 0) => h = -1

---------------------------------------------------------------------------
(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

Termination == <>(pc = "Done")

=============================================================================
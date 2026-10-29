---------------------------- MODULE MCFindHighest ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the FindHighest specification.              *)
(* Bounds the length of the sequence f by MaxLength and restricts the      *)
(* naturals to the finite range 0..MaxNat. The FindHighest algorithm is    *)
(* inlined so that this module parses on its own.                          *)
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

\* All sequences over S whose length is at most MaxLength
SeqOf(S) == UNION { [1..n -> S] : n \in 0..MaxLength }

\* Bounded replacement for Seq(Nat)
BoundedSeqNat == SeqOf(BoundedNat)

Max(a, b) == IF a >= b THEN a ELSE b

---------------------------------------------------------------------------
(***************************************************************************)
(* FindHighest (inlined)                                                   *)
(*                                                                         *)
(*   variables f \in Seq(Nat), h = -1, i = 1;                              *)
(*   while i <= Len(f) do                                                  *)
(*     if f[i] > h then h := f[i] end if;                                  *)
(*     i := i + 1;                                                         *)
(*   end while;                                                            *)
(***************************************************************************)

VARIABLES f, h, i, pc

vars == << f, h, i, pc >>

Init ==
    /\ f \in BoundedSeqNat
    /\ h = -1
    /\ i = 1
    /\ pc = "lb"

Loop ==
    /\ pc = "lb"
    /\ i <= Len(f)
    /\ h' = Max(h, f[i])
    /\ i' = i + 1
    /\ pc' = "lb"
    /\ UNCHANGED f

Finish ==
    /\ pc = "lb"
    /\ i > Len(f)
    /\ pc' = "Done"
    /\ UNCHANGED << f, h, i >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Loop \/ Finish \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop \/ Finish)

---------------------------------------------------------------------------
(***************************************************************************)
(* Model constraint                                                        *)
(***************************************************************************)

StateConstraint == Len(f) <= MaxLength

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

TypeOK ==
    /\ f \in BoundedSeqNat
    /\ h \in BoundedNat \cup {-1}
    /\ i \in 1..(Len(f) + 1)
    /\ pc \in {"lb", "Done"}

\* Loop invariant: h is the max of the elements examined so far
LoopInvariant ==
    /\ \A j \in 1..(i - 1) : f[j] <= h
    /\ (i > 1) => (\E j \in 1..(i - 1) : f[j] = h)
    /\ (i = 1) => (h = -1)

\* On termination h is the highest element of f (or -1 if f is empty)
Correctness ==
    pc = "Done" =>
        /\ \A j \in 1..Len(f) : f[j] <= h
        /\ (Len(f) > 0) => (\E j \in 1..Len(f) : f[j] = h)
        /\ (Len(f) = 0) => (h = -1)

---------------------------------------------------------------------------
(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

Termination == <>(pc = "Done")

=============================================================================
---------------------------- MODULE MCFindHighest ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the FindHighest specification.  It           *)
(* introduces the constants MaxLength and MaxNat, bounds the length of the *)
(* sequence f to at most MaxLength, and restricts naturals to the finite   *)
(* range 0..MaxNat.  Helper operators: a bounded natural set and a         *)
(* constructor for all sequences over a set S (up to length MaxLength).    *)
(* The FindHighest algorithm is included inline so that this module is     *)
(* self-contained and can be parsed and model-checked on its own.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxLength, MaxNat

ASSUME MaxLength \in Nat /\ MaxNat \in Nat

---------------------------------------------------------------------------
(* Model helper operators *)

\* Finite stand-in for Nat
BoundedNat == 0 .. MaxNat

\* All sequences over S whose length is at most MaxLength
SeqOf(S) == UNION { [1 .. n -> S] : n \in 0 .. MaxLength }

\* Finite stand-in for Seq(Nat)
BoundedSeqNat == SeqOf(BoundedNat)

---------------------------------------------------------------------------
(* FindHighest algorithm *)

VARIABLES f, h, i, pc

vars == << f, h, i, pc >>

Max(a, b) == IF a >= b THEN a ELSE b

Init ==
  /\ f \in BoundedSeqNat
  /\ h = -1
  /\ i = 1
  /\ pc = "lb"

Loop ==
  /\ pc = "lb"
  /\ IF i <= Len(f)
       THEN /\ h' = Max(h, f[i])
            /\ i' = i + 1
            /\ UNCHANGED << f, pc >>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << f, h, i >>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Loop \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------
(* Model constraints *)

\* Bound the length of the sequence f
StateConstraint == Len(f) <= MaxLength

---------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
  /\ f \in BoundedSeqNat
  /\ h \in BoundedNat \cup {-1}
  /\ i \in 1 .. (Len(f) + 1)
  /\ pc \in {"lb", "Done"}

\* h is the maximum of all elements examined so far
InductiveInvariant ==
  /\ \A idx \in 1 .. (i - 1) : f[idx] <= h
  /\ (i > 1) => \E idx \in 1 .. (i - 1) : f[idx] = h
  /\ (i = 1) => h = -1

\* Upon termination, h is the highest element of f (or -1 if f is empty)
Correctness ==
  pc = "Done" =>
    /\ \A idx \in DOMAIN f : f[idx] <= h
    /\ (Len(f) > 0) => \E idx \in DOMAIN f : f[idx] = h
    /\ (Len(f) = 0) => h = -1

---------------------------------------------------------------------------
(* Liveness *)

Termination == <>(pc = "Done")

=============================================================================
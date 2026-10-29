----------------------------- MODULE FindHighest -----------------------------
EXTENDS Integers, Sequences

CONSTANTS MaxLength, MaxNat

ASSUME MaxLength \in Nat /\ MaxNat \in Nat

(***************************************************************************)
(* Bounded replacements for Nat and Seq. The configuration substitutes     *)
(* them as  Nat <- MCNat  and  Seq <- MCSeq.                               *)
(***************************************************************************)
MCNat == 0 .. MaxNat

MCSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. MaxLength }

VARIABLES f, h, i, pc

vars == << f, h, i, pc >>

Max(a, b) == IF a >= b THEN a ELSE b

(***************************************************************************)
(* The input sequence is chosen nondeterministically from all sequences   *)
(* that respect the bounds. h holds the highest value seen so far. It is  *)
(* -1 when no element has been seen. i is the next index to examine.      *)
(***************************************************************************)
Init ==
  /\ f \in Seq(Nat)
  /\ h = -1
  /\ i = 1
  /\ pc = "lb"

lb ==
  /\ pc = "lb"
  /\ IF i <= Len(f)
       THEN /\ h' = Max(h, f[i])
            /\ i' = i + 1
            /\ pc' = "lb"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << h, i >>
  /\ f' = f

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == lb \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1 .. (Len(f) + 1)
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

(* Accessed indices and element values stay within the stated bounds. *)
BoundsOK ==
  /\ Len(f) <= MaxLength
  /\ \A idx \in DOMAIN f : f[idx] \in 0 .. MaxNat
  /\ h \in -1 .. MaxNat
  /\ i \in 1 .. (MaxLength + 1)

InductiveInvariant ==
  /\ TypeOK
  /\ \A idx \in 1 .. (i - 1) : f[idx] <= h
  /\ (h = -1) <=> (i = 1)
  /\ (h /= -1) => \E idx \in 1 .. (i - 1) : f[idx] = h
  /\ (pc = "Done") => (i = Len(f) + 1)

(* On termination, every index has been examined. *)
DoneIndexValue ==
  pc = "Done" => i = Len(f) + 1

(***************************************************************************)
(* Safety. On termination, h = -1 means "no maximum". This happens exactly *)
(* when f is empty. Otherwise h is an element of f, and it is at least as  *)
(* large as every element of f.                                            *)
(***************************************************************************)
Correctness ==
  pc = "Done" =>
    /\ \A idx \in DOMAIN f : f[idx] <= h
    /\ (h = -1) <=> (f = << >>)
    /\ (h /= -1) => \E idx \in DOMAIN f : f[idx] = h

(* Liveness: the procedure eventually reports a result. *)
Termination == <>(pc = "Done")

MCConstraint ==
  /\ Len(f) <= MaxLength
  /\ i <= MaxLength + 1

=============================================================================
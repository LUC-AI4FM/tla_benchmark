---------------------------- MODULE FindHighest ----------------------------
EXTENDS Sequences, Naturals, Integers

(***************************************************************************)
(* Finds the maximum element of a finite sequence of natural numbers.      *)
(*                                                                         *)
(*   f : the input sequence                                                *)
(*   h : the highest value seen so far (-1 is the initial sentinel)        *)
(*   i : the index of the next element to examine                          *)
(*   pc: the program counter ("lb" while looping, "Done" when finished)    *)
(***************************************************************************)

VARIABLES f, h, i, pc

vars == << f, h, i, pc >>

(* Bounds so that TLC can enumerate initial sequences.                    *)
(* Logically, every input is an element of Seq(Nat).                      *)
MaxSeqLen == 3
MaxElemVal == 3

BoundedSeqNat ==
    UNION { [1..n -> 0..MaxElemVal] : n \in 0..MaxSeqLen }

Init ==
    /\ f \in BoundedSeqNat
    /\ h = -1
    /\ i = 1
    /\ pc = "lb"

lb ==
    /\ pc = "lb"
    /\ IF i <= Len(f)
          THEN /\ h' = IF f[i] > h THEN f[i] ELSE h
               /\ i' = i + 1
               /\ pc' = "lb"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << h, i >>
    /\ UNCHANGED f

(* Allows infinite stuttering after termination, so TLC reports no deadlock. *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == lb \/ Terminating

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Type safety *)
TypeOK ==
    /\ f \in Seq(Nat)
    /\ i \in Nat
    /\ i \in 1..(Len(f) + 1)
    /\ h \in Nat \cup {-1}
    /\ pc \in {"lb", "Done"}

(* Partial correctness: h dominates every element examined so far. *)
InductiveInvariant ==
    \A idx \in 1..(i - 1) : f[idx] <= h

(* Termination implies all elements have been processed. *)
DoneIndexValue ==
    pc = "Done" => i = Len(f) + 1

(* Total correctness: on termination, h dominates every element of f. *)
Correctness ==
    pc = "Done" => \A idx \in DOMAIN f : f[idx] <= h

THEOREM Spec => []TypeOK
THEOREM Spec => []InductiveInvariant
THEOREM Spec => []DoneIndexValue
THEOREM Spec => []Correctness

=============================================================================
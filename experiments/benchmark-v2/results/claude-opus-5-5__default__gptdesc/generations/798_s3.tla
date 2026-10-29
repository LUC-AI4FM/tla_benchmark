---------------------------- MODULE FindHighest -----------------------------
(***************************************************************************)
(* Specifies and proves correctness of a simple algorithm that finds the   *)
(* largest value in a sequence of natural numbers. The algorithm walks     *)
(* through the sequence f with index i and keeps the highest value seen so *)
(* far in h. Once it terminates, h is >= every element of f. After it      *)
(* terminates, the spec allows infinite stuttering so there is no deadlock.*)
(***************************************************************************)
EXTENDS Sequences, Naturals, Integers, TLAPS

(****************************************************************************
--algorithm Highest {
  variables
    f \in Seq(Nat);
    h = -1;
    i = 1;
  define {
    max(a, b) == IF a >= b THEN a ELSE b
  } {
lb: while (i <= Len(f)) {
      h := max(h, f[i]);
      i := i + 1;
    }
  }
}
****************************************************************************)
\* BEGIN TRANSLATION
VARIABLES f, h, i, pc

(* define statement *)
max(a, b) == IF a >= b THEN a ELSE b

vars == << f, h, i, pc >>

Init == (* Global variables *)
        /\ f \in Seq(Nat)
        /\ h = -1
        /\ i = 1
        /\ pc = "lb"

lb == /\ pc = "lb"
      /\ IF i <= Len(f)
            THEN /\ h' = max(h, f[i])
                 /\ i' = i + 1
                 /\ pc' = "lb"
            ELSE /\ pc' = "Done"
                 /\ UNCHANGED << h, i >>
      /\ f' = f

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Type invariant.                                                         *)
(***************************************************************************)
TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1..(Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

THEOREM TypeInvariantHolds == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars
               PROVE TypeOK'
    OBVIOUS
  <2>1. CASE lb
    BY <2>1 DEF TypeOK, lb, max
  <2>2. CASE Terminating
    BY <2>2 DEF TypeOK, Terminating, vars
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF TypeOK, vars
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1> QED
  BY PTL, <1>1, <1>2 DEF Spec

(***************************************************************************)
(* Inductive invariant: h is >= every element already visited.            *)
(***************************************************************************)
InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
  BY DEF Init, InductiveInvariant
<1>2. TypeOK /\ InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  <2> SUFFICES ASSUME TypeOK, InductiveInvariant, [Next]_vars
               PROVE InductiveInvariant'
    OBVIOUS
  <2>1. CASE lb
    BY <2>1 DEF TypeOK, InductiveInvariant, lb, max
  <2>2. CASE Terminating
    BY <2>2 DEF InductiveInvariant, Terminating, vars
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF InductiveInvariant, vars
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1> QED
  BY PTL, <1>1, <1>2, TypeInvariantHolds DEF Spec

(***************************************************************************)
(* Helper property: once the algorithm is done, i = Len(f) + 1.            *)
(***************************************************************************)
DoneIndexValue ==
  pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
<1>1. Init => DoneIndexValue
  BY DEF Init, DoneIndexValue
<1>2. TypeOK /\ DoneIndexValue /\ [Next]_vars => DoneIndexValue'
  <2> SUFFICES ASSUME TypeOK, DoneIndexValue, [Next]_vars
               PROVE DoneIndexValue'
    OBVIOUS
  <2>1. CASE lb
    BY <2>1 DEF TypeOK, DoneIndexValue, lb
  <2>2. CASE Terminating
    BY <2>2 DEF DoneIndexValue, Terminating, vars
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF DoneIndexValue, vars
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1> QED
  BY PTL, <1>1, <1>2, TypeInvariantHolds DEF Spec

(***************************************************************************)
(* Correctness: on termination, h is >= every element of f.                *)
(***************************************************************************)
Correctness ==
  pc = "Done" => \A idx \in DOMAIN f : f[idx] <= h

THEOREM IsCorrect == Spec => []Correctness
<1>1. TypeOK /\ InductiveInvariant /\ DoneIndexValue => Correctness
  <2> SUFFICES ASSUME TypeOK, InductiveInvariant, DoneIndexValue,
                      pc = "Done"
               PROVE \A idx \in DOMAIN f : f[idx] <= h
    BY DEF Correctness
  <2>1. i = Len(f) + 1
    BY DEF DoneIndexValue
  <2>2. DOMAIN f = 1..Len(f)
    BY DEF TypeOK
  <2> QED
    BY <2>1, <2>2 DEF TypeOK, InductiveInvariant
<1> QED
  BY PTL, <1>1, TypeInvariantHolds, InductiveInvariantHolds,
     DoneIndexValueThm

=============================================================================
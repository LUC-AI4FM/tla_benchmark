---------------------------- MODULE FindHighest ----------------------------
(***************************************************************************)
(* Specifies and proves correctness of a very simple algorithm that finds *)
(* the largest value in a sequence of natural numbers.  The algorithm     *)
(* iterates through the sequence f, keeps the highest value seen so far   *)
(* in h, and advances the index i until it has passed the end of f.  After *)
(* termination, h is greater than or equal to every element of f.         *)
(* The algorithm allows infinite stuttering after termination, so it does *)
(* not deadlock.                                                          *)
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

(* Fair version of the specification, under which Termination holds. *)
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Type invariant.                                                          *)
(***************************************************************************)
TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in Nat
  /\ i \in 1..(Len(f) + 1)
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

THEOREM IsTypeOK == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY DEF Init, TypeOK
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    BY DEF TypeOK, Next, vars, lb, Terminating, max
  <1>3. QED
    BY PTL, <1>1, <1>2 DEF Spec

(***************************************************************************)
(* Inductive invariant: h is at least every element already examined.      *)
(***************************************************************************)
InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
  <1>1. Init => InductiveInvariant
    BY DEF Init, InductiveInvariant
  <1>2. TypeOK /\ InductiveInvariant /\ [Next]_vars => InductiveInvariant'
    BY DEF TypeOK, InductiveInvariant, Next, vars, lb, Terminating, max
  <1>3. QED
    BY PTL, <1>1, <1>2, IsTypeOK DEF Spec

(***************************************************************************)
(* Helper property: once done, the index is one past the end of f.         *)
(***************************************************************************)
DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
  <1>1. Init => DoneIndexValue
    BY DEF Init, DoneIndexValue
  <1>2. TypeOK /\ DoneIndexValue /\ [Next]_vars => DoneIndexValue'
    BY DEF TypeOK, DoneIndexValue, Next, vars, lb, Terminating
  <1>3. QED
    BY PTL, <1>1, <1>2, IsTypeOK DEF Spec

(***************************************************************************)
(* Correctness: after termination h is >= every element of f.              *)
(***************************************************************************)
Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

THEOREM IsCorrect == Spec => []Correctness
  <1>1. TypeOK /\ InductiveInvariant /\ DoneIndexValue => Correctness
    BY DEF TypeOK, InductiveInvariant, DoneIndexValue, Correctness
  <1>2. QED
    BY PTL, <1>1, IsTypeOK, InductiveInvariantHolds, DoneIndexValueThm

=============================================================================
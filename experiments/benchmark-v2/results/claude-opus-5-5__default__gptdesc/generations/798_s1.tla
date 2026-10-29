---------------------------- MODULE FindHighest -----------------------------
(***************************************************************************)
(* Specifies and proves correctness of a very simple algorithm that finds  *)
(* the largest value in a sequence of natural numbers. The algorithm       *)
(* iterates through the sequence f, keeps the current highest value in h,  *)
(* and advances the index i until it terminates. After termination, h is   *)
(* greater than or equal to every element of f.                            *)
(*                                                                         *)
(* Infinite stuttering after termination is allowed on purpose, so the     *)
(* spec does not deadlock.                                                 *)
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
  /\ i \in Nat
  /\ i \in 1..(Len(f) + 1)
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

THEOREM TypeInvariantHolds == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
    OBVIOUS
  <2>1. CASE lb
    BY <2>1 DEF lb, TypeOK, max
  <2>2. CASE Terminating
    BY <2>2 DEF Terminating, TypeOK, vars
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF TypeOK, vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY PTL, <1>1, <1>2 DEF Spec

(***************************************************************************)
(* Inductive invariant: h is at least every element already visited.       *)
(***************************************************************************)
InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
<1> DEFINE Inv == TypeOK /\ InductiveInvariant
<1>1. Init => Inv
  BY DEF Init, TypeOK, InductiveInvariant
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. TypeOK'
    BY TypeInvariantHolds DEF TypeOK, Next, lb, Terminating, vars, max
  <2>2. CASE lb
    <3>1. CASE i <= Len(f)
      BY <2>2, <3>1 DEF lb, TypeOK, InductiveInvariant, max
    <3>2. CASE ~(i <= Len(f))
      BY <2>2, <3>2 DEF lb, TypeOK, InductiveInvariant
    <3>3. QED
      BY <2>1, <3>1, <3>2
  <2>3. CASE Terminating
    BY <2>1, <2>3 DEF Terminating, vars, InductiveInvariant
  <2>4. CASE UNCHANGED vars
    BY <2>1, <2>4 DEF vars, InductiveInvariant
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1>3. QED
  BY PTL, <1>1, <1>2 DEF Spec

(***************************************************************************)
(* Helper property: upon termination, i is one past the end of f.          *)
(***************************************************************************)
DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
<1> DEFINE Inv == TypeOK /\ DoneIndexValue
<1>1. Init => Inv
  BY DEF Init, TypeOK, DoneIndexValue
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE lb
    BY <2>1 DEF lb, TypeOK, DoneIndexValue, max
  <2>2. CASE Terminating
    BY <2>2 DEF Terminating, vars, TypeOK, DoneIndexValue
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, TypeOK, DoneIndexValue
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY PTL, <1>1, <1>2 DEF Spec

(***************************************************************************)
(* Correctness: after termination, h is >= every element of f.             *)
(***************************************************************************)
Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

THEOREM IsCorrect == Spec => []Correctness
<1>1. TypeOK /\ InductiveInvariant /\ DoneIndexValue => Correctness
  BY DEF TypeOK, InductiveInvariant, DoneIndexValue, Correctness
<1>2. QED
  BY PTL, <1>1, TypeInvariantHolds, InductiveInvariantHolds, DoneIndexValueThm

=============================================================================
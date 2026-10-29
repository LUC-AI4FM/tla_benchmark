---------------------------- MODULE FindHighest ----------------------------
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

\* Type invariant
TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1 .. (Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

\* Inductive invariant: h is at least every element seen so far
InductiveInvariant ==
  \A idx \in 1 .. (i - 1) : f[idx] <= h

\* Once the algorithm terminates, the index is one past the end
DoneIndexValue == pc = "Done" => i = Len(f) + 1

\* Correctness: on termination, h is >= every element of f
Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

THEOREM TypeInvariantHolds == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
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
  BY <1>1, <1>2, PTL DEF Spec

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
    BY <2>2 DEF TypeOK, InductiveInvariant, Terminating, vars
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF TypeOK, InductiveInvariant, vars
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1> QED
  BY <1>1, <1>2, TypeInvariantHolds, PTL DEF Spec

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
    BY <2>2 DEF TypeOK, DoneIndexValue, Terminating, vars
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF TypeOK, DoneIndexValue, vars
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1> QED
  BY <1>1, <1>2, TypeInvariantHolds, PTL DEF Spec

THEOREM IsCorrect == Spec => []Correctness
<1>1. TypeOK /\ InductiveInvariant /\ DoneIndexValue => Correctness
  BY DEF TypeOK, InductiveInvariant, DoneIndexValue, Correctness
<1> QED
  BY <1>1, TypeInvariantHolds, InductiveInvariantHolds,
     DoneIndexValueThm, PTL

=============================================================================
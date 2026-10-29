---------------------------- MODULE FindHighest -----------------------------
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

-----------------------------------------------------------------------------

TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1..(Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

THEOREM TypeInvariantHolds == Spec => []TypeOK
PROOF
  <1>a. Init => TypeOK
    BY DEFS Init, TypeOK
  <1>b. TypeOK /\ UNCHANGED vars => TypeOK'
    BY DEFS TypeOK, vars
  <1>c. TypeOK /\ Next => TypeOK'
    <2>a. TypeOK /\ lb => TypeOK'
      BY DEFS TypeOK, lb, max
    <2>b. TypeOK /\ Terminating => TypeOK'
      BY DEFS TypeOK, Terminating, vars
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec

InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF
  <1>a. Init => InductiveInvariant
    BY DEFS Init, InductiveInvariant
  <1>b. InductiveInvariant /\ UNCHANGED vars => InductiveInvariant'
    BY DEFS InductiveInvariant, vars
  <1>c. TypeOK /\ InductiveInvariant /\ Next => InductiveInvariant'
    <2>a. TypeOK /\ InductiveInvariant /\ lb => InductiveInvariant'
      BY DEFS TypeOK, InductiveInvariant, lb, max
    <2>b. TypeOK /\ InductiveInvariant /\ Terminating => InductiveInvariant'
      BY DEFS TypeOK, InductiveInvariant, Terminating, vars
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec

DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
PROOF
  <1>a. Init => DoneIndexValue
    BY DEF Init, DoneIndexValue
  <1>b. DoneIndexValue /\ UNCHANGED vars => DoneIndexValue'
    BY DEFS DoneIndexValue, vars
  <1>c. TypeOK /\ DoneIndexValue /\ Next => DoneIndexValue'
    <2>a. TypeOK /\ DoneIndexValue /\ lb => DoneIndexValue'
      BY DEFS TypeOK, lb, DoneIndexValue
    <2>b. TypeOK /\ DoneIndexValue /\ Terminating => DoneIndexValue'
      BY DEFS TypeOK, Terminating, vars, DoneIndexValue
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec

Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

THEOREM IsCorrect == Spec => []Correctness
PROOF
  <1>a. TypeOK /\ InductiveInvariant /\ DoneIndexValue => Correctness
    BY DEFS TypeOK, InductiveInvariant, DoneIndexValue, Correctness
  <1> QED BY PTL, <1>a, TypeInvariantHolds, InductiveInvariantHolds, DoneIndexValueThm

=============================================================================
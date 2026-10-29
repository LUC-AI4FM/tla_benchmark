---------------------------- MODULE FindHighest ----------------------------
(***************************************************************************)
(* A simple algorithm that finds the highest value in a sequence of        *)
(* natural numbers by iterating through it and tracking the maximum value  *)
(* seen so far.                                                            *)
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

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1..(Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}

THEOREM TypeInvariantHolds == Spec => []TypeOK
PROOF
  <1>a. Init => TypeOK
    BY DEFS Init, TypeOK
  <1>b. TypeOK /\ [Next]_vars => TypeOK'
    <2>. SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
      OBVIOUS
    <2>a. CASE Next
      BY <2>a DEFS Next, Terminating, TypeOK, lb, max, vars
    <2>b. CASE UNCHANGED vars
      BY <2>b DEFS TypeOK, vars
    <2>. QED BY <2>a, <2>b
  <1>. QED BY PTL, <1>a, <1>b DEF Spec

(***************************************************************************)
(* Inductive invariant: all previously examined elements are <= h.         *)
(***************************************************************************)
InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF
  <1>a. Init => InductiveInvariant
    BY DEFS Init, InductiveInvariant
  <1>b. TypeOK /\ InductiveInvariant /\ [Next]_vars => InductiveInvariant'
    <2>. SUFFICES ASSUME TypeOK, InductiveInvariant, [Next]_vars
                  PROVE InductiveInvariant'
      OBVIOUS
    <2>a. CASE Next
      BY <2>a DEFS Next, Terminating, InductiveInvariant, TypeOK, lb, max, vars
    <2>b. CASE UNCHANGED vars
      BY <2>b DEFS InductiveInvariant, vars
    <2>. QED BY <2>a, <2>b
  <1>. QED BY PTL, <1>a, <1>b, TypeInvariantHolds DEF Spec

(***************************************************************************)
(* Upon termination, the index equals Len(f) + 1.                          *)
(***************************************************************************)
DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
PROOF
  <1>a. Init => DoneIndexValue
    BY DEF Init, DoneIndexValue
  <1>b. TypeOK /\ DoneIndexValue /\ [Next]_vars => DoneIndexValue'
    <2>. SUFFICES ASSUME TypeOK, DoneIndexValue, [Next]_vars
                  PROVE DoneIndexValue'
      OBVIOUS
    <2>a. CASE Next
      BY <2>a DEFS Next, Terminating, DoneIndexValue, TypeOK, lb, vars
    <2>b. CASE UNCHANGED vars
      BY <2>b DEFS DoneIndexValue, vars
    <2>. QED BY <2>a, <2>b
  <1>. QED BY PTL, <1>a, <1>b, TypeInvariantHolds DEF Spec

(***************************************************************************)
(* Correctness: upon termination, h is >= every element of f.             *)
(***************************************************************************)
Correctness ==
  pc = "Done" => \A idx \in DOMAIN f : f[idx] <= h

THEOREM IsCorrect == Spec => []Correctness
PROOF
  <1>. SUFFICES ASSUME TypeOK, InductiveInvariant, DoneIndexValue
                PROVE Correctness
    BY PTL, TypeInvariantHolds, InductiveInvariantHolds, DoneIndexValueThm
  <1>. QED BY DEFS Correctness, TypeOK, InductiveInvariant, DoneIndexValue

(***************************************************************************)
(* Termination (defined above as Termination) is not proven here.          *)
(***************************************************************************)

=============================================================================
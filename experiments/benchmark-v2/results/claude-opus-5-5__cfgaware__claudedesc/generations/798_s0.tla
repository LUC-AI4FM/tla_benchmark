---------------------------- MODULE FindHighest ----------------------------
EXTENDS Sequences, Naturals, Integers, TLAPS

(*--algorithm Highest
variables
  f \in Seq(Nat);
  h = -1;
  i = 1;
define
  max(a, b) == IF a >= b THEN a ELSE b
end define;
begin
lb: while i <= Len(f) do
      h := max(h, f[i]);
      i := i + 1;
    end while;
end algorithm; *)

VARIABLES f, h, i, pc

max(a, b) == IF a >= b THEN a ELSE b

vars == << f, h, i, pc >>

Init == /\ f \in Seq(Nat)
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

Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* Type invariant
TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1..(Len(f) + 1)
  /\ h \in Nat \cup {-1}
  /\ pc \in {"lb", "Done"}

\* When the loop has finished, the index is one past the end of the sequence
DoneIndexValue == pc = "Done" => i = Len(f) + 1

\* All previously examined elements are bounded by h
InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

\* Upon termination, h is at least every element of f
Correctness ==
  pc = "Done" => \A idx \in DOMAIN f : f[idx] <= h

-----------------------------------------------------------------------------
\* Proofs

THEOREM TypeInvariantHolds == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, lb, Terminating, vars, max
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM DoneIndexValueHolds == Spec => []DoneIndexValue
<1>1. Init => DoneIndexValue
  BY DEF Init, DoneIndexValue
<1>2. TypeOK /\ DoneIndexValue /\ [Next]_vars => DoneIndexValue'
  BY DEF TypeOK, DoneIndexValue, Next, lb, Terminating, vars
<1>3. QED
  BY <1>1, <1>2, TypeInvariantHolds, PTL DEF Spec

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
  BY DEF Init, InductiveInvariant
<1>2. TypeOK /\ InductiveInvariant /\ [Next]_vars => InductiveInvariant'
  BY DEF TypeOK, InductiveInvariant, Next, lb, Terminating, vars, max
<1>3. QED
  BY <1>1, <1>2, TypeInvariantHolds, PTL DEF Spec

THEOREM IsCorrect == Spec => []Correctness
<1>1. TypeOK /\ DoneIndexValue /\ InductiveInvariant => Correctness
  BY DEF TypeOK, DoneIndexValue, InductiveInvariant, Correctness
<1>2. QED
  BY <1>1, TypeInvariantHolds, DoneIndexValueHolds,
     InductiveInvariantHolds, PTL

=============================================================================
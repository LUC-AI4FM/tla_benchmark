------------------------------- MODULE NonDetQuickSort -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  N,            \* Array length
  Values,       \* Totally ordered domain of values
  Leq,          \* Non-strict total order relation on Values: Leq ⊆ Values × Values
  AInit         \* Initial array (sequence) of length N over Values

ASSUME
  /\ N \in Nat
  /\ AInit \in Seq(Values) /\ Len(AInit) = N
  /\ Leq \subseteq Values \X Values
  /\ \A x \in Values : <<x, x>> \in Leq
  /\ \A x, y \in Values : (<<x, y>> \in Leq /\ <<y, x>> \in Leq) => x = y
  /\ \A x, y, z \in Values : (<<x, y>> \in Leq /\ <<y, z>> \in Leq) => <<x, z>> \in Leq
  /\ \A x, y \in Values : (<<x, y>> \in Leq) \/ (<<y, x>> \in Leq)

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
  A,   \* current array (sequence) of length N over Values
  P    \* pending intervals (work set)

Idx == 1..N

Intervals ==
  { [lo |-> i, hi |-> j] \in [lo : Idx, hi : Idx] : i <= j }

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)

Count(s, v) ==
  Cardinality({ i \in DOMAIN s : s[i] = v })

Permutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \A v \in Values : Count(s, v) = Count(t, v)

Sorted(arr) ==
  \A i \in 1..(Len(arr) - 1) : <<arr[i], arr[i+1]>> \in Leq

TypeOK ==
  /\ A \in Seq(Values) /\ Len(A) = N
  /\ P \subseteq Intervals

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ A = AInit
  /\ P = IF N = 0 THEN {} ELSE { [lo |-> 1, hi |-> N] }

(***************************************************************************)
(* Transition relation                                                     *)
(***************************************************************************)

PartitionStep(I) ==
  \E p \in I.lo..(I.hi - 1) :
  \E B \in Seq(Values) :
    /\ Len(B) = N
    /\ \A k \in (Idx \ (I.lo..I.hi)) : B[k] = A[k]
    /\ Permutation(SubSeq(B, I.lo, I.hi), SubSeq(A, I.lo, I.hi))
    /\ \A i \in I.lo..p : \A j \in (p + 1)..I.hi : <<B[i], B[j]>> \in Leq
    /\ A' = B
    /\ P' = (P \ {I}) \cup { [lo |-> I.lo, hi |-> p], [lo |-> p + 1, hi |-> I.hi] }

RemoveStep(I) ==
  /\ I.lo = I.hi
  /\ A' = A
  /\ P' = P \ {I}

Next ==
  \E I \in P :
    IF I.lo < I.hi
      THEN PartitionStep(I)
      ELSE RemoveStep(I)

vars == << A, P >>

(***************************************************************************)
(* Specification and properties                                            *)
(***************************************************************************)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

NoPending == P = {}

SafetyInvariant ==
  /\ TypeOK
  /\ Permutation(A, AInit)

OrderingWhenDone ==
  [] (NoPending => Sorted(A))

Termination ==
  Spec => <> NoPending

=============================================================================
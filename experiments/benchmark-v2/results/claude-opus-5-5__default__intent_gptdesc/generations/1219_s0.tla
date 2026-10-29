------------------------------ MODULE UnchangedSemantics ------------------------------
(***************************************************************************)
(* A small deterministic state space with a finite indexed collection x   *)
(* (a function 1..N -> Nat) and a scalar counter y.  Each step either      *)
(* stutters or increments the counter while leaving x unchanged.  The      *)
(* spec states which derived expressions must stay UNCHANGED whenever x    *)
(* is unchanged, and records any violation in a history flag.              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,      \* number of indexed data elements
          MaxY    \* bound on the counter (keeps the state space finite)

ASSUME NAssump    == N \in Nat /\ N >= 2
ASSUME MaxYAssump == MaxY \in Nat

VARIABLES x,          \* indexed data elements
          y,          \* scalar counter
          violation   \* history flag: TRUE iff a derived expression ever
                      \* changed while x did not

vars == <<x, y, violation>>

D == 1..N

\* Known, distinct initial values of the indexed elements
InitVal(i) == 10 * i
InitX      == [i \in D |-> InitVal(i)]
InitY      == 0

-----------------------------------------------------------------------------
(* Derived expressions over the indexed data *)

Elem1        == x[1]
Elem2        == x[2]
Rec          == [a |-> x[1], b |-> x[2]]
ExistsPred   == \E i \in D : x[i] = InitVal(1)
ForallPred   == \A i \in D : x[i] > 0
ChooseIdx    == CHOOSE i \in D : x[i] = InitVal(1)
ChooseMax    == CHOOSE i \in D : \A j \in D : x[j] <= x[i]
ValueSet     == {x[i] : i \in D}
FilterSet    == {i \in D : x[i] > InitVal(1)}
QuantSet     == {i \in D : \E j \in D : x[j] > x[i]}
QuantSet2    == {i \in D : \A j \in D : x[j] >= x[i]}
DomX         == DOMAIN x
CardValues   == Cardinality({x[i] : i \in D})

(* Syntactically different but semantically constant expressions *)
ConstDiff    == x[1] - x[1]                         \* always 0
ConstEmpty   == {x[i] : i \in {}}                   \* always {}
ConstTrue    == \E i \in D : x[i] = x[i]            \* always TRUE
ConstFalse   == \A i \in D : x[i] # x[i]            \* always FALSE (N >= 1)
ConstDom     == DOMAIN [i \in D |-> x[i]]           \* always D

\* Every indexed element individually unchanged
EachElemUnchanged == \A i \in D : UNCHANGED x[i]

\* All derived expressions unchanged
DerivedUnchanged ==
    /\ EachElemUnchanged
    /\ UNCHANGED Elem1
    /\ UNCHANGED Elem2
    /\ UNCHANGED Rec
    /\ UNCHANGED <<x[1], x[2]>>
    /\ UNCHANGED ExistsPred
    /\ UNCHANGED ForallPred
    /\ UNCHANGED ChooseIdx
    /\ UNCHANGED ChooseMax
    /\ UNCHANGED ValueSet
    /\ UNCHANGED FilterSet
    /\ UNCHANGED QuantSet
    /\ UNCHANGED QuantSet2
    /\ UNCHANGED DomX
    /\ UNCHANGED CardValues
    /\ UNCHANGED ConstDiff
    /\ UNCHANGED ConstEmpty
    /\ UNCHANGED ConstTrue
    /\ UNCHANGED ConstFalse
    /\ UNCHANGED ConstDom

-----------------------------------------------------------------------------
(* Initial state and transitions *)

Init ==
    /\ x = InitX
    /\ y = InitY
    /\ violation = FALSE

\* Bookkeeping for the history flag; evaluated after x' and y' are fixed
UpdateViolation ==
    violation' = (violation \/ (UNCHANGED x /\ ~DerivedUnchanged))

Stutter ==
    /\ UNCHANGED <<x, y>>
    /\ UpdateViolation

Increment ==
    /\ y < MaxY
    /\ y' = y + 1
    /\ UNCHANGED x
    /\ UpdateViolation

Next == Increment \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

-----------------------------------------------------------------------------
(* Safety: invariants *)

TypeOK ==
    /\ x \in [D -> Nat]
    /\ y \in 0..MaxY
    /\ violation \in BOOLEAN

\* Indexed elements always retain their initial values
XInitInv == x = InitX
ElemInitInv == \A i \in D : x[i] = InitVal(i)

\* Initial values are distinct
DistinctInv == \A i, j \in D : i # j => x[i] # x[j]

\* Derived expressions keep their expected (initial) values
DerivedValueInv ==
    /\ Rec = [a |-> InitVal(1), b |-> InitVal(2)]
    /\ ExistsPred
    /\ ForallPred
    /\ ChooseIdx = 1
    /\ ChooseMax = N
    /\ ValueSet = {InitVal(i) : i \in D}
    /\ FilterSet = 2..N
    /\ QuantSet = 1..(N-1)
    /\ QuantSet2 = {1}
    /\ DomX = D
    /\ CardValues = N
    /\ ConstDiff = 0
    /\ ConstEmpty = {}
    /\ ConstTrue
    /\ ~ConstFalse
    /\ ConstDom = D

\* Safety flag: no derived expression has ever changed while x did not
NoViolation == violation = FALSE

Invariants ==
    /\ TypeOK
    /\ XInitInv
    /\ ElemInitInv
    /\ DistinctInv
    /\ DerivedValueInv
    /\ NoViolation

-----------------------------------------------------------------------------
(* Safety: action properties *)

\* Any step modifying the counter leaves every indexed element unchanged
CounterStepKeepsX ==
    [][(y' # y) => (UNCHANGED x /\ EachElemUnchanged)]_vars

\* Counter only ever increases by one
CounterMonotone ==
    [][(y' = y) \/ (y' = y + 1)]_vars

\* All derived expressions are unchanged whenever x is unchanged
DerivedUnchangedProp ==
    [][UNCHANGED x => DerivedUnchanged]_vars

\* x is never modified by any step
XNeverChanges ==
    [][UNCHANGED x]_vars

\* Semantically constant expressions are unchanged across every step
ConstExprsUnchanged ==
    [][ /\ UNCHANGED ConstDiff
        /\ UNCHANGED ConstEmpty
        /\ UNCHANGED ConstTrue
        /\ UNCHANGED ConstFalse
        /\ UNCHANGED ConstDom ]_vars

-----------------------------------------------------------------------------
(* Liveness (trivial, under weak fairness of Increment) *)

CounterReachesMax == <>(y = MaxY)
EventuallyStable  == <>[](y = MaxY)

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => CounterStepKeepsX /\ DerivedUnchangedProp /\ ConstExprsUnchanged
THEOREM Spec => CounterReachesMax
=============================================================================
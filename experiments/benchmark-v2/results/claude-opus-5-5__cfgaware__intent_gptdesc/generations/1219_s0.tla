---------------------------- MODULE UnchangedSemantics ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* A small deterministic system with an indexed collection x (a function  *)
(* over 1..3) and a scalar counter c. Steps either stutter or increment   *)
(* c while keeping x unchanged. The history variables px and pc record    *)
(* the previous values of x and c, so state invariants can check          *)
(* properties of steps.                                                    *)
(***************************************************************************)

VARIABLES x, c, px, pc

vars == <<x, c, px, pc>>

Idx    == 1..3
MaxC   == 3
X0     == [i \in Idx |-> i * 10]   \* distinct initial values 10, 20, 30
C0     == 0

(***************************************************************************)
(* Expressions derived from an indexed collection f                        *)
(***************************************************************************)
Elem1(f)   == f[1]
Elem2(f)   == f[2]
Elem3(f)   == f[3]
Rec(f)     == [a |-> f[1], b |-> f[2], d |-> f[3]]
ExP(f)     == \E i \in DOMAIN f : f[i] = 20
AllP(f)    == \A i \in DOMAIN f : f[i] > 0
Ch(f)      == CHOOSE i \in DOMAIN f : f[i] = 30
SetOf(f)   == {f[i] : i \in DOMAIN f}
SetQ(f)    == {i \in DOMAIN f : \E j \in DOMAIN f : f[j] > f[i]}
SetQAll(f) == {i \in DOMAIN f : \A j \in DOMAIN f : f[j] <= f[i]}
Dom(f)     == DOMAIN f

\* Syntactically different from a literal but semantically constant
SemConst1(f) == f[1] - f[1]
SemConst2(f) == SetOf(f) \cup {}
SemConst3(f) == {i \in DOMAIN f : f[i] # f[i]}

Derived(f) ==
    <<Elem1(f), Elem2(f), Elem3(f), Rec(f), ExP(f), AllP(f), Ch(f),
      SetOf(f), SetQ(f), SetQAll(f), Dom(f),
      SemConst1(f), SemConst2(f), SemConst3(f)>>

DerivedSame(f, g) ==
    /\ Elem1(f)     = Elem1(g)
    /\ Elem2(f)     = Elem2(g)
    /\ Elem3(f)     = Elem3(g)
    /\ Rec(f)       = Rec(g)
    /\ ExP(f)       = ExP(g)
    /\ AllP(f)      = AllP(g)
    /\ Ch(f)        = Ch(g)
    /\ SetOf(f)     = SetOf(g)
    /\ SetQ(f)      = SetQ(g)
    /\ SetQAll(f)   = SetQAll(g)
    /\ Dom(f)       = Dom(g)
    /\ SemConst1(f) = SemConst1(g)
    /\ SemConst2(f) = SemConst2(g)
    /\ SemConst3(f) = SemConst3(g)

(***************************************************************************)
(* Initial state and transitions                                           *)
(***************************************************************************)
Init ==
    /\ x  = X0
    /\ c  = C0
    /\ px = X0
    /\ pc = C0

Stutter ==
    /\ UNCHANGED <<x, c>>
    /\ px' = x
    /\ pc' = c

Inc ==
    /\ c < MaxC
    /\ c' = c + 1
    /\ UNCHANGED x
    /\ px' = x
    /\ pc' = c

Next == Inc \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* State invariants. Because px and pc hold the previous state, these     *)
(* invariants also check properties of steps.                              *)
(***************************************************************************)
TypeOK ==
    /\ x  \in [Idx -> Nat]
    /\ px \in [Idx -> Nat]
    /\ c  \in 0..MaxC
    /\ pc \in 0..MaxC

InitValuesKept ==
    /\ x = X0
    /\ \A i \in Idx : x[i] = i * 10

CounterStepPreservesData ==
    (pc # c) => (px = x /\ \A i \in Idx : px[i] = x[i])

DerivedUnchanged ==
    (\A i \in Idx : px[i] = x[i]) => DerivedSame(px, x)

\* Safety flag: true if a derived expression changed while the elements did not
Violation ==
    /\ \A i \in Idx : px[i] = x[i]
    /\ Derived(px) # Derived(x)

SemanticConstants ==
    /\ SemConst1(x) = 0
    /\ SemConst2(x) = {10, 20, 30}
    /\ SemConst3(x) = {}
    /\ Ch(x) = 3
    /\ SetQ(x) = {1, 2}
    /\ SetQAll(x) = {3}
    /\ Dom(x) = Idx
    /\ Rec(x) = [a |-> 10, b |-> 20, d |-> 30]

Inv ==
    /\ TypeOK
    /\ InitValuesKept
    /\ CounterStepPreservesData
    /\ DerivedUnchanged
    /\ ~Violation
    /\ SemanticConstants

(***************************************************************************)
(* Action-level properties that state the semantics of UNCHANGED directly *)
(***************************************************************************)
UnchangedAction ==
    UNCHANGED x =>
        /\ UNCHANGED x[1]
        /\ UNCHANGED x[2]
        /\ UNCHANGED x[3]
        /\ UNCHANGED [a |-> x[1], b |-> x[2], d |-> x[3]]
        /\ UNCHANGED (\E i \in DOMAIN x : x[i] = 20)
        /\ UNCHANGED (\A i \in DOMAIN x : x[i] > 0)
        /\ UNCHANGED (CHOOSE i \in DOMAIN x : x[i] = 30)
        /\ UNCHANGED {x[i] : i \in DOMAIN x}
        /\ UNCHANGED {i \in DOMAIN x : \E j \in DOMAIN x : x[j] > x[i]}
        /\ UNCHANGED {i \in DOMAIN x : \A j \in DOMAIN x : x[j] <= x[i]}
        /\ UNCHANGED DOMAIN x
        /\ UNCHANGED (x[1] - x[1])

IncKeepsData == [][(c' # c) => UNCHANGED x]_vars
UnchangedProp == [][UnchangedAction]_vars
Liveness      == <>(c = MaxC)

=============================================================================
---------------------------- MODULE BoundedNatStateMachine ----------------------------
EXTENDS Naturals

CONSTANTS
    MaxVal,     \* upper bound of the finite natural-number domain
    InitVal     \* the unique initial value

ASSUME MaxValIsNat  == MaxVal \in Nat
ASSUME InitValInDom == InitVal \in 0..MaxVal

VARIABLE x

vars == << x >>

\* The bounded numeric type: a finite set of natural numbers
Domain == 0..MaxVal

-----------------------------------------------------------------------------------------
\* Type invariant
TypeOK == x \in Domain

\* Unique initial state
Init == x = InitVal

-----------------------------------------------------------------------------------------
\* Allowed kinds of updates (some may produce values outside Domain)

\* Unconditional assignment to a fixed value
ResetToZero == x' = 0

\* Unconditional assignment to a fixed value that may lie outside the domain
JumpBeyond == x' = MaxVal + 1

\* Next value in a contiguous subrange, independent of the current value
ChooseLowRange == x' \in 1..3

\* Next value in a contiguous subrange that may exceed the domain
ChooseHighRange == x' \in (MaxVal - 1)..(MaxVal + 2)

\* Guarded transitions: specific current values enable specific next values
GuardedFromInit == x = InitVal /\ x' = InitVal

GuardedFromOne  == x = 1 /\ x' \in {2, 4}

GuardedFromTwo  == x = 2 /\ x' \in 5..7

GuardedFromMax  == x = MaxVal /\ x' = MaxVal + 3

\* Raw (unconstrained) transition relation
RawNext ==
    \/ ResetToZero
    \/ JumpBeyond
    \/ ChooseLowRange
    \/ ChooseHighRange
    \/ GuardedFromInit
    \/ GuardedFromOne
    \/ GuardedFromTwo
    \/ GuardedFromMax

\* Choices contradicting the bounded type are disallowed
Next == RawNext /\ x' \in Domain

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------------
\* Safety properties

\* Type safety: the variable never leaves the prescribed finite domain
TypeSafety == TypeOK

\* Global invariant: type-correctness together with preservation of the initial value
Inv == TypeOK /\ x = InitVal

THEOREM Spec => []TypeSafety
THEOREM Spec => []Inv

=========================================================================================
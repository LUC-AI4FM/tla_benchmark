------------------------------ MODULE FrozenInvariantDemo ------------------------------

EXTENDS Naturals, Integers

CONSTANTS
    FIXED, \* a fixed natural to assign to x
    RANGE_MAX, \* upper bound of a small range for assignment
    SMALL, \* small bound used by the invariant's type constraint
    OUT \* a specific out-of-range value

ASSUME FIXED \in Nat /\ FIXED # 0
ASSUME RANGE_MAX \in Nat /\ RANGE_MAX >= 1
ASSUME SMALL \in Nat
ASSUME OUT \in Int /\ OUT \notin 0..SMALL

VARIABLES x

Init ==
    x = 0

SetFixed ==
    x' = FIXED

SetInRange ==
    x' \in 1..RANGE_MAX

SetOutOfRange ==
    x' = OUT

MapA ==
    x = 1 /\ x' = 2

MapB ==
    x = 3 /\ x' = 5

Next ==
    SetFixed \/ SetInRange \/ SetOutOfRange \/ MapA \/ MapB

TypeInv ==
    x \in 0..SMALL

ZeroInv ==
    x = 0

Inv ==
    TypeInv /\ ZeroInv

Spec ==
    Init /\ []Inv /\ [][Next]_x

=============================================================================
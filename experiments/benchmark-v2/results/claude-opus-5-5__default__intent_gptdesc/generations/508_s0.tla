---------------------------- MODULE SquareAssert ----------------------------
EXTENDS Integers, TLC

CONSTANTS Lo, Hi

ASSUME /\ Lo \in Int
       /\ Hi \in Int
       /\ Lo = 1
       /\ Hi = 10

VARIABLES x, pc

vars == << x, pc >>

Range == Lo..Hi

TypeOK ==
    /\ x \in Range
    /\ pc \in {"A", "Done"}

Init ==
    /\ x \in Range
    /\ pc = "A"

A ==
    /\ pc = "A"
    /\ Assert(x * x <= 100, "Failure of assertion: x * x <= 100")
    /\ pc' = "Done"
    /\ UNCHANGED x

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == A \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

SquareBound == x * x <= 100

SafetyInv == TypeOK /\ SquareBound

StaysDone == [][pc = "Done" => pc' = "Done"]_vars

THEOREM Spec => []SafetyInv
THEOREM Spec => Termination
=============================================================================
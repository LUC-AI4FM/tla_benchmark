---------------------------- MODULE PositiveAssign ----------------------------
EXTENDS Naturals

CONSTANT NoValue

ASSUME NoValueAssumption == NoValue \notin {0, 1}

VARIABLE x

vars == << x >>

Choices == {0, 1}

Accept(v) == v > 0

PossibleNext == { v \in Choices : Accept(v) }

ASSUME PossibleNextIsSingleton == PossibleNext = {1}

Init == x = NoValue

Attempt(v) ==
    IF Accept(v)
       THEN x' = v
       ELSE UNCHANGED x

AcceptingAssign == \E v \in Choices : Accept(v) /\ x' = v

Next == \E v \in Choices : Attempt(v)

Spec == Init /\ [][Next]_vars /\ WF_vars(AcceptingAssign)

-----------------------------------------------------------------------------

TypeOK == x \in Choices \cup {NoValue}

Safety == (x # NoValue) => (x \in Choices)

AcceptedIsPositive ==
    [][ (x' # x) => (x' \in PossibleNext /\ x' = 1) ]_vars

NextValuesSingleton ==
    [][ (x' # x) => (x' \in {1}) ]_vars

ZeroNeverAccepted == [][ x' # 0 ]_vars

PositiveStaysLegal == [](x = 1 => [](x \in Choices))

EventuallyPositive == <>(x = 1)

THEOREM Spec => []TypeOK
THEOREM Spec => []Safety
THEOREM Spec => AcceptedIsPositive
THEOREM Spec => NextValuesSingleton
THEOREM Spec => ZeroNeverAccepted
THEOREM Spec => PositiveStaysLegal
THEOREM Spec => EventuallyPositive
=============================================================================
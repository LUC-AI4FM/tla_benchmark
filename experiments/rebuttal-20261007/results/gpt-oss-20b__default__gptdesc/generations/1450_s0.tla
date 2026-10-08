MODULE RandomSubsetSpec
EXTENDS Naturals, TLC

CONSTANT RandomSubsetSet

VARIABLE x

S == 1..9
T == 1..10

FuncType == [s \in S |-> t \in T]

Init == /\ x \in RandomSubsetSet
       /\ RandomSubsetSet \subseteq FuncType
       /\ #RandomSubsetSet = 1000

Next == x' = x

Inv == TRUE

Spec == Init /\ [][Next]_x /\ []Inv
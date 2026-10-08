MODULE Counter
EXTENDS Naturals

CONSTANT Max == 10

VARIABLE counter

Init == counter = 0

Increment == counter < Max /\ counter' = counter + 1

Halt == counter = Max /\ counter' = counter

Next == Increment \/ Halt

Spec == Init /\ [][Next]_<<counter>> /\ WF_0(Increment)

Inv == counter <= Max /\ counter >= 0

THEOREM Safety == Spec => [] Inv

THEOREM Termination == Spec => <> (counter = Max)

THEOREM UniqueFive == Spec => []((counter = 5) => <> (counter > 5))

THEOREM UniqueNine == Spec => []((counter = 9) => <> (counter > 9))
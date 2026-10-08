-------------------------------- MODULE I --------------------------------

VARIABLE x

S == {1, 2, 3, 4, 5}

Init == x \in S

N(i) == UNCHANGED <<x>>

Next == \E i \in {1, 2, 3} : N(i)

F == [i \in S |-> IF i = 1 THEN 1 ELSE F[i-1] + 1]

Inv == \E i \in DOMAIN F : F[i] = x

Spec == Init /\ [][Next]_x

==========================================================================
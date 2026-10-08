```tla
MODULE HandshakeChannel

EXTENDS Naturals, FiniteSets

CONSTANTS ValueSet

VARIABLES ch

Init == /\ ch.val \in ValueSet
        /\ ch.rdy = 0
        /\ ch.ack = 0

Next == \/ /\ ch.rdy = ch.ack
           /\ \/ /\ ch'.rdy = (ch.rdy + 1) % 2
              /\ ch'.val \in ValueSet
              /\ ch'.ack = ch.ack
         \/ /\ ch.rdy # ch.ack
            /\ ch'.ack = (ch.ack + 1) % 2
            /\ ch'.rdy = ch.rdy
            /\ ch'.val = ch.val

TypeInvariant == /\ ch.rdy \in {0, 1}
                 /\ ch.ack \in {0, 1}

Spec ==
    Init /\ [][Next]_<<ch>> /\ WF_next(<<ch>>)

WF_next(vars) == \/ vars' \in Next
                  \/ \<exists> x \in vars : x' = x

THEOREM Spec => []TypeInvariant
```
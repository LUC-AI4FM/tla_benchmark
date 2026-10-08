------------------------------ MODULE HandshakeChannel ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS ValueSet

VARIABLES ch

Init == /\ ch = [val |-> ArbValue, rdy |-> 0, ack |-> 0]
        /\ ArbValue \in ValueSet

Next == \/ /\ ch[rdy] = ch[ack]
            /\ \/ /\ ch[val]' \in ValueSet
               /\ ch[rdy]' = 1 - ch[rdy]
               /\ ch[ack]' = ch[ack]
           \/ /\ ch[val]' = ch[val]
              /\ ch[rdy]' = ch[rdy]
              /\ ch[ack]' = ch[ack]
        \/ /\ ch[rdy] # ch[ack]
            /\ ch[val]' = ch[val]
               /\ ch[rdy]' = ch[rdy]
               /\ ch[ack]' = 1 - ch[ack]

TypeInvariant == /\ ch[rdy] \in {0, 1}
                 /\ ch[ack] \in {0, 1}
                 /\ ch[val] \in ValueSet

Spec == Init /\ [][Next]_<<ch>> /\ WF_next(<<ch>>)

WF_next(vars) == \/ <>(\E x \in vars: Enabled(next(x)))
                 \/ [](Enabled(next(vars)) => <>(next(vars)))

=============================================================================
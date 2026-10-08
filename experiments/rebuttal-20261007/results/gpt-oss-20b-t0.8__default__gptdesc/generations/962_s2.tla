---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals

VARIABLES sb, rb, ab

(* Bit domain *)
Bits == {0, 1}

Init ==
    /\ sb \in Bits
    /\ rb \in Bits
    /\ ab \in Bits
    /\ sb = 0
    /\ rb = 1
    /\ ab = 1

SendAction ==
    /\ ab = sb
    /\ sb' = 1 - sb
    /\ UNCHANGED <<rb, ab>>

ReceiveAction ==
    /\ rb != sb
    /\ rb' = 1 - rb
    /\ UNCHANGED <<sb, ab>>

AckRecAction ==
    /\ rb != ab
    /\ ab' = 1 - ab
    /\ UNCHANGED <<sb, rb>>

Next == \/ SendAction \/ ReceiveAction \/ AckRecAction

TypeInvariant == /\ sb \in Bits
               /\ rb \in Bits
               /\ ab \in Bits

(* Liveness: sender and acknowledgement bits are infinitely often out of sync *)
InfSync == []<>(sb /= ab)

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(ReceiveAction)
    /\ WF_vars(AckRecAction)
    /\ []TypeInvariant
    /\ InfSync

=============================================================================
------------------------------- MODULE HandshakeChannel -------------------------------

VARIABLES ch

CONSTANTS ValSet

ASSUME ValSet \subseteq Nat /\ Cardinality(ValSet) > 0

(*--algorithm handshake_channel
variables ch = [val \in ValSet |-> 0, rdy \in {0, 1} |-> 0, ack \in {0, 1} |-> 0]
begin
    while TRUE do
        with
            /\ \/ /\ ch.rdy = ch.ack
                 /\ \/ /\ ch.val \in ValSet
                      /\ ch' = [ch EXCEPT !.rdy = 1 - ch.rdy, !.val = CHOOSE v \in ValSet : v]
                 \/ /\ ch.rdy # ch.ack
                    /\ ch' = [ch EXCEPT !.ack = 1 - ch.ack]
        end with;
    od;
end algorithm;*)

TypeInvariant == 
    /\ ch.val \in ValSet
    /\ ch.rdy \in {0, 1}
    /\ ch.ack \in {0, 1}

Init ==
    /\ ch.val \in ValSet
    /\ ch.rdy = 0
    /\ ch.ack = 0

Next ==
    \/ /\ ch.rdy = ch.ack
       /\ \/ /\ ch.val \in ValSet
            /\ ch' = [ch EXCEPT !.rdy = 1 - ch.rdy, !.val = CHOOSE v \in ValSet : v]
       \/ /\ ch.rdy # ch.ack
          /\ ch' = [ch EXCEPT !.ack = 1 - ch.ack]

Spec ==
    Init /\ [][Next]_<<ch>>

=============================================================================
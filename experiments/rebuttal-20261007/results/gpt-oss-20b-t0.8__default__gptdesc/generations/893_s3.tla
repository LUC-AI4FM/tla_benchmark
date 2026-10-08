------------------------------ MODULE ChannelSpec ------------------------------
EXTENDS Naturals
VARIABLE ch

(* Initial state *)
Init == ch = [val |-> 0, rdy |-> 0, ack |-> 0]

(* Sender action: can send any natural value when rdy equals ack. *)
Send ==
  ∃ v ∈ Nat :
    /\ ch.rdy = ch.ack
    /\ ch' = [ch EXCEPT !.rdy = 1 - ch.rdy, !.val = v]

(* Receiver action: can receive when rdy and ack differ. *)
Receive ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ch EXCEPT !.ack = 1 - ch.ack]

Next == Send \/ Receive

(* Type invariant for the channel record *)
TypeInv == (ch.rdy ∈ {0,1}) /\ (ch.ack ∈ {0,1}) /\ (ch.val ∈ Nat)

Spec == Init /\ [][Next]_ch

THEOREM TypeInvariantPreserved == Spec => []TypeInv
=============================================================================
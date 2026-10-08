--------------------------- MODULE ChannelHandshake ---------------------------
EXTENDS INT

VARIABLE ch

(* --- Initial state ----------------------------------------------------- *)
Init ==
  ch = [val |-> 0, rdy |-> 0, ack |-> 0]

(* --- Actions ------------------------------------------------------------ *)
Send ==
  /\ ch.rdy = ch.ack
  /\ \E v \in Int :
       ch' = [ch EXCEPT ! .val = v,
                      ! .rdy = 1 - ch.rdy]
          (* ack unchanged *)

Receive ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ch EXCEPT ! .ack = 1 - ch.ack]
          (* rdy and val unchanged *)

Next == Send \/ Receive

(* --- Invariant ---------------------------------------------------------- *)
TypeInv ==
  /\ ch.rdy \in {0,1}
  /\ ch.ack \in {0,1}
  /\ ch.val \in Int

(* --- Specification ------------------------------------------------------ *)
Spec == Init /\ []Next

(* --- Property to be proved ---------------------------------------------- *)
THEOREM TypeInvariant:
  Spec => []TypeInv
=============================================================================
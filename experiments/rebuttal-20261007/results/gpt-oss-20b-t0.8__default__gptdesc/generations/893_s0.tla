------------------------------ MODULE HandshakeChannel ------------------------------
EXTENDS Naturals

VARIABLE ch

(* ------------------------------------------------------------------------- *)
(* The channel is a record with fields:
   val : a natural number
   rdy : 0 or 1 (ready bit)
   ack : 0 or 1 (acknowledge bit)                                   *)
(* ------------------------------------------------------------------------- *)

Init ==
  ch = [val |-> 0, rdy |-> 0, ack |-> 0]

Send(v) ==
  v \in Nat
  /\ ch.rdy = ch.ack
  /\ ch' = [ch EXCEPT !.rdy = 1 - ch.rdy,
                        !.val = v]

Receive ==
  ch.rdy # ch.ack
  /\ ch' = [ch EXCEPT !.ack = 1 - ch.ack]

Next == (\E v \in Nat : Send(v)) \/ Receive

TypeInv ==
  ch.rdy \in {0,1}
  /\ ch.ack \in {0,1}
  /\ ch.val \in Nat

Spec == Init
       /\ []Next

(* ------------------------------------------------------------------------- *)
(* Safety invariant: the type of the channel is preserved at all times.      *)
(* ------------------------------------------------------------------------- *)

TypeInvariant == [] TypeInv
=============================================================================
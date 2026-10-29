---------------------------- MODULE Channel ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLE chan

vars == << chan >>

TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

-----------------------------------------------------------------------------

Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

Send(d) == /\ chan.rdy = chan.ack
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv == /\ chan.rdy # chan.ack
       /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant

(***************************************************************************)
(* Model-checking configuration (Channel.cfg):                             *)
(*   CONSTANT Data = {d1, d2, d3}                                          *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANT TypeInvariant                                               *)
(* where d1, d2, d3 are model values.                                      *)
(***************************************************************************)
=============================================================================
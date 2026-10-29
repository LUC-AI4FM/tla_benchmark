--------------------------- MODULE APChannel ----------------------------------
(***************************************************************************)
(* Apalache type annotations for FIFO/Channel.tla.                         *)
(*                                                                         *)
(* This module is a typed wrapper.  It declares the constant Data and the  *)
(* variable chan with Apalache type annotations, and then instantiates     *)
(* Channel.  The original Channel module stays free of tool-specific       *)
(* details.  Init, Next, Spec and TypeInvariant come from the INSTANCE.    *)
(*                                                                         *)
(* A copy of Channel is included as an inner module so that this file      *)
(* parses on its own with SANY.  It is placed before the outer             *)
(* declarations so that it does not inherit them.                          *)
(***************************************************************************)
EXTENDS Integers

  ------------------------------ MODULE Channel ------------------------------
  CONSTANT Data
  VARIABLE chan

  TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

  Init == /\ TypeInvariant
          /\ chan.ack = chan.rdy

  Send(d) == /\ chan.rdy = chan.ack
             /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

  Rcv == /\ chan.rdy # chan.ack
         /\ chan' = [chan EXCEPT !.ack = 1 - @]

  Next == (\E d \in Data : Send(d)) \/ Rcv

  Spec == Init /\ [][Next]_chan

  THEOREM Spec => []TypeInvariant
  =============================================================================
------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache type annotations for FIFO/Channel.tla.  The original Channel   *)
(* specification is kept free of tool-specific details; type information  *)
(* is attached here, and Channel is brought in through INSTANCE.           *)
(*                                                                         *)
(* A copy of Channel is included as a submodule so that this file parses  *)
(* on its own.  It is declared before the outer CONSTANT and VARIABLE so   *)
(* that its declarations do not clash with them.                           *)
(***************************************************************************)
EXTENDS Integers

  ------------------------------ MODULE Channel ------------------------------
  CONSTANT Data
  VARIABLE chan

  TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]
  ---------------------------------------------------------------------------
  Init == /\ TypeInvariant
          /\ chan.ack = chan.rdy

  Send(d) == /\ chan.rdy = chan.ack
             /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

  Rcv == /\ chan.rdy # chan.ack
         /\ chan' = [chan EXCEPT !.ack = 1 - @]

  Next == (\E d \in Data : Send(d)) \/ Rcv

  Spec == Init /\ [][Next]_chan
  ---------------------------------------------------------------------------
  THEOREM Spec => []TypeInvariant
  ============================================================================
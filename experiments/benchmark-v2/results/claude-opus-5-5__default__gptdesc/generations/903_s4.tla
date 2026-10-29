---------------------------- MODULE APChannel ----------------------------
(***************************************************************************)
(* Apalache type annotations for the Channel module of Specifying Systems. *)
(* The Channel module is included as a nested submodule so that this      *)
(* specification is self-contained and parses on its own.                 *)
(***************************************************************************)
EXTENDS Naturals

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
  ===========================================================================
------------------------------ MODULE APChannel ------------------------------
(***************************************************************************)
(* Apalache type annotations for the Channel module used throughout the    *)
(* Specifying Systems repository.  The Channel specification is included   *)
(* below as an inner module so that this file is self-contained and can be *)
(* parsed by SANY on its own.  The outer module declares the typed         *)
(* constant Data and the typed variable chan, instantiates Channel, and    *)
(* provides a concrete value DataVal for Data for model checking.          *)
(***************************************************************************)

    ---------------------------- MODULE Channel ----------------------------
    EXTENDS Naturals

    CONSTANT Data

    VARIABLE chan

    TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]
    --------------------------------------------------------------------------
    Init == /\ TypeInvariant
            /\ chan.ack = chan.rdy

    Send(d) == /\ chan.rdy = chan.ack
               /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

    Rcv == /\ chan.rdy # chan.ack
           /\ chan' = [chan EXCEPT !.ack = 1 - @]

    Next == (\E d \in Data : Send(d)) \/ Rcv

    Spec == Init /\ [][Next]_chan
    --------------------------------------------------------------------------
    THEOREM Spec => []TypeInvariant
    ==========================================================================
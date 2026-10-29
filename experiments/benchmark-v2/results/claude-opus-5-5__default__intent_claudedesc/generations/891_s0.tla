--------------------------- MODULE AsynchInterface ---------------------------
(***************************************************************************)
(* A simple asynchronous interface between a sender and a receiver that    *)
(* communicate over a one-place buffer, using a two-phase ready/acknowledge *)
(* handshake with single-bit toggle signals.                               *)
(*                                                                         *)
(*   val : the data value currently on the channel                         *)
(*   rdy : the ready bit, toggled by the sender when it sends a value      *)
(*   ack : the acknowledge bit, toggled by the receiver when it accepts    *)
(*                                                                         *)
(* The sender may send only when rdy = ack.  The receiver may accept only  *)
(* when rdy # ack.                                                         *)
(*                                                                         *)
(* For model checking with TLC, instantiate Data with a concrete finite    *)
(* set, e.g. in the model configuration:                                   *)
(*     CONSTANT Data = {d1, d2, d3}   (model values)                       *)
(*     SPECIFICATION Spec                                                  *)
(*     INVARIANT TypeInvariant                                             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

vars == <<val, rdy, ack>>

(***************************************************************************)
(* Type invariant: val is a data value, rdy and ack are single bits.       *)
(***************************************************************************)
TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}

-----------------------------------------------------------------------------

(***************************************************************************)
(* Initial state: any state satisfying the type constraints in which the   *)
(* acknowledge signal equals the ready signal (the channel is empty).      *)
(***************************************************************************)
Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy

(***************************************************************************)
(* The sender sends a new value: enabled only when rdy = ack.  It sets the *)
(* data value and toggles rdy.                                             *)
(***************************************************************************)
Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

(***************************************************************************)
(* The receiver accepts the value: enabled only when rdy # ack.  It        *)
(* toggles ack so that it matches rdy again.                               *)
(***************************************************************************)
Rcv == /\ rdy # ack
       /\ ack' = 1 - ack
       /\ UNCHANGED <<val, rdy>>

Next == Send \/ Rcv

(***************************************************************************)
(* The complete specification, allowing stuttering steps.                  *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant

=============================================================================
------------------------------ MODULE Channel ------------------------------
EXTENDS Naturals, TLC

CONSTANT Data

VARIABLE chan

(* ------------------------------------------------------------------ *)
(*  Type invariant for the channel record                              *)
(* ------------------------------------------------------------------ *)
TypeInvariant == /\ chan.val \in Data
                 /\ chan.rdy \in BOOLEAN
                 /\ chan.ack \in BOOLEAN

(* ------------------------------------------------------------------ *)
(*  Initial state: type invariant holds and no message in transit     *)
(* ------------------------------------------------------------------ *)
Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

(* ------------------------------------------------------------------ *)
(*  Send action: channel idle (rdy = ack) → place value d and toggle rdy *)
(* ------------------------------------------------------------------ *)
Send(d) ==
  /\ d \in Data
  /\ chan.rdy = chan.ack
  /\ chan' = [chan EXCEPT !.val = d, !.rdy = ~chan.rdy]

(* ------------------------------------------------------------------ *)
(*  Receive action: message pending (rdy # ack) → toggle ack          *)
(* ------------------------------------------------------------------ *)
Rcv ==
  /\ chan.rdy # chan.ack
  /\ chan' = [chan EXCEPT !.ack = ~chan.ack]

(* ------------------------------------------------------------------ *)
(*  Stuttering step: do nothing                                       *)
(* ------------------------------------------------------------------ *)
Stutter == chan' = chan

(* ------------------------------------------------------------------ *)
(*  Next-state relation (stuttering‑tolerant)                          *)
(* ------------------------------------------------------------------ *)
Next == \/ \E d \in Data : Send(d)
        \/ Rcv
        \/ Stutter

(* ------------------------------------------------------------------ *)
(*  Temporal specification                                               *)
(* ------------------------------------------------------------------ *)
Spec == Init /\ [] Next

(* ------------------------------------------------------------------ *)
(*  Invariant theorem                                                   *)
(* ------------------------------------------------------------------ *)
THEOREM TypeInvariant_I : Spec => []TypeInvariant

END MODULE
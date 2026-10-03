MODULE ABCSpec

VARIABLE sb, rb, sd, rd

(* Type invariant *)
TypeInv == /\ sb \in BOOLEAN
          /\ rb \in BOOLEAN
          /\ sd \in Nat
          /\ rd \in Nat

(* Initial condition *)
Init == /\ sb = FALSE
        /\ rb = FALSE
        /\ sd = 0
        /\ rd = 0

(* Sender may send a new value when its acknowledgement bit matches its send bit *)
SenderSend ==
    /\ rb = sb
    /\ sd' \in Nat
    /\ sb' = ~ sb
    /\ rb' = rb
    /\ rd' = rd

(* Receiver may accept a message when its receive bit differs from the sender bit *)
ReceiverAccept ==
    /\ sb # rb
    /\ rd' = sd
    /\ rb' = ~ rb
    /\ sb' = sb
    /\ sd' = sd

Next == SenderSend \/ ReceiverAccept

FairnessAssumptions == []<>(SenderSend) /\ []<>(ReceiverAccept)

Spec == Init /\ [][Next]_<<sb,rb,sd,rd>> /\ FairnessAssumptions

(* Safety property: type invariant holds always *)
SafetyProp == []TypeInv

(* Temporal property: sender and acknowledgement bits are infinitely often out of sync *)
InfSyncOutOfSync == []<>(sb # rb)
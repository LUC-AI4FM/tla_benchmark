MODULE AsyncInterface
CONSTANTS DATASET

VARIABLES ready, ack, data

(* Type invariant *)
TypeInv == 
  /\ ready ∈ {0,1}
  /\ ack ∈ {0,1}
  /\ data ∈ DATASET

Init == TypeInv /\ (ack = ready)

Sender ==
  /\ ready = ack
  /\ data' ∈ DATASET
  /\ ready' = 1 - ready
  /\ ack' = ack

Receiver ==
  /\ ready # ack
  /\ data' = data
  /\ ack' = ready
  /\ ready' = ready

Stutter ==
  /\ ready' = ready
  /\ ack' = ack
  /\ data' = data

Next == Sender \/ Receiver \/ Stutter

Spec == Init /\ [][Next]_vars

Inv == []TypeInv
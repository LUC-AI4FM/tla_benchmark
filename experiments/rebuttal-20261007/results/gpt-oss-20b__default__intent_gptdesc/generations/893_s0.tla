MODULE HandshakeChannel

EXTENDS Naturals, TLC

CONSTANTS DataSet

VARIABLES data, rdy, ack, last

(* Type invariant *)
TypeInv == /\ data ∈ DataSet
          /\ rdy ∈ {0,1}
          /\ ack ∈ {0,1}
          /\ last ∈ {"init","send","recv"}

(* Initial state: channel holds a valid data element and readiness and acknowledgement bits start equal. *)
Init == /\ data ∈ DataSet
        /\ rdy = 0
        /\ ack = 0
        /\ last = "init"

(* Send action: allowed only when rdy = ack; flips readiness bit and sets new data. *)
Send(newData) ==
    /\ rdy = ack
    /\ newData ∈ DataSet
    /\ data'   = newData
    /\ rdy'    = 1 - rdy
    /\ ack'    = ack
    /\ last'   = "send"

(* Receive action: allowed only when rdy ≠ ack; flips acknowledgement bit to match readiness. *)
Recv ==
    /\ rdy # ack
    /\ data'   = data
    /\ rdy'    = rdy
    /\ ack'    = rdy
    /\ last'   = "recv"

Next == ∃ newData ∈ DataSet : Send(newData) \/ Recv

(* Invariant: ready equals ack only at initialization or after a receiver step acknowledges. *)
ReadyAckInvariant == (rdy = ack) => (last = "init" \/ last = "recv")

Inv == TypeInv /\ ReadyAckInvariant

Spec == Init
        /\ [][Next]_<<data,rdy,ack,last>>
        /\ WF_∃[Next]_<<data,rdy,ack,last>>
        /\ []Inv

===============================================================================
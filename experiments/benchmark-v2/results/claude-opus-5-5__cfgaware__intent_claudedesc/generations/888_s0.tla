---------------------------- MODULE AsynchInterface ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

vars == <<val, rdy, ack>>

(* A concrete finite set of data values used to instantiate Data *)
DataVal == {"d1", "d2", "d3"}

TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}

-------------------------------------------------------------------------------

Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy

(* Sender: when the previous value has been acknowledged (rdy = ack),
   place a new value on the channel and toggle rdy. *)
Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

(* Receiver: when a new value is available (rdy # ack),
   consume it and toggle ack to acknowledge. *)
Rcv == /\ rdy # ack
       /\ ack' = 1 - ack
       /\ UNCHANGED <<val, rdy>>

Next == Send \/ Rcv

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

-------------------------------------------------------------------------------

(* Correctness properties *)

(* Alternation: sends and receives strictly alternate *)
Alternation == [][ (rdy = ack => ~Rcv) /\ (rdy # ack => ~Send) ]_vars

(* Sender never overwrites unacknowledged data *)
NoOverwrite == [][ (rdy # ack) => (val' = val) ]_vars

(* Progress: every sent value is eventually acknowledged *)
EventuallyReceived == (rdy # ack) ~> (rdy = ack)

(* Progress: the system keeps transferring data *)
ContinuousProgress == []<>(rdy # ack) /\ []<>(rdy = ack)

THEOREM Spec => []TypeInvariant
================================================================================
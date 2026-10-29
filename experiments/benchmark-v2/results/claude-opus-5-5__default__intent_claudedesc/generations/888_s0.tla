--------------------------- MODULE AsynchInterface ---------------------------
(***************************************************************************)
(* Two-phase handshake between a sender and a receiver with no shared     *)
(* clock. They coordinate through two single-bit signals:                 *)
(*   rdy : written only by the sender                                     *)
(*   ack : written only by the receiver                                   *)
(* val is the data wire, which only the sender writes.                    *)
(*                                                                         *)
(* When rdy = ack, the channel is empty and the sender may send.          *)
(* When rdy # ack, a value is pending and the receiver may receive.       *)
(*                                                                         *)
(* Two history variables are used only to state correctness:              *)
(*   sent : the sequence of values the sender has transmitted             *)
(*   rcvd : the sequence of values the receiver has consumed              *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLES val, rdy, ack, sent, rcvd

vars == <<val, rdy, ack, sent, rcvd>>

TypeInvariant ==
    /\ val  \in Data
    /\ rdy  \in {0, 1}
    /\ ack  \in {0, 1}
    /\ sent \in Seq(Data)
    /\ rcvd \in Seq(Data)

---------------------------------------------------------------------------
Init ==
    /\ val  \in Data
    /\ rdy  \in {0, 1}
    /\ ack  = rdy
    /\ sent = << >>
    /\ rcvd = << >>

(* Sender: only when the previous value has been acknowledged.            *)
(* It places a new value on the wire and toggles rdy.                     *)
Send ==
    /\ rdy = ack
    /\ \E d \in Data :
          /\ val'  = d
          /\ sent' = Append(sent, d)
    /\ rdy' = 1 - rdy
    /\ UNCHANGED <<ack, rcvd>>

(* Receiver: only when a fresh value is pending.                          *)
(* It consumes the value and toggles ack.                                 *)
Rcv ==
    /\ rdy # ack
    /\ rcvd' = Append(rcvd, val)
    /\ ack'  = 1 - ack
    /\ UNCHANGED <<val, rdy, sent>>

Next == Send \/ Rcv

Fairness == WF_vars(Send) /\ WF_vars(Rcv)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                      *)
(***************************************************************************)

(* The received values are exactly a prefix of the sent values, in the   *)
(* same order. So nothing is invented, reordered, or duplicated.         *)
NoDuplicationOrCorruption ==
    /\ Len(rcvd) <= Len(sent)
    /\ SubSeq(sent, 1, Len(rcvd)) = rcvd

(* At most one value is ever in transit. The sender never overwrites an   *)
(* unacknowledged value.                                                  *)
AtMostOneInTransit ==
    Len(sent) - Len(rcvd) \in {0, 1}

(* The handshake signals agree with the channel state. When a value is    *)
(* pending, the wire holds the most recently sent value. This means the   *)
(* receiver never reads stale or invalid data.                           *)
ProperSynchronization ==
    /\ (rdy = ack) => (Len(sent) = Len(rcvd))
    /\ (rdy # ack) => /\ Len(sent) = Len(rcvd) + 1
                      /\ val = sent[Len(sent)]

Safety ==
    /\ TypeInvariant
    /\ NoDuplicationOrCorruption
    /\ AtMostOneInTransit
    /\ ProperSynchronization

(* Send and receive phases strictly alternate.                            *)
Alternation ==
    [][ (Send => rdy = ack) /\ (Rcv => rdy # ack) ]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                    *)
(***************************************************************************)

(* No data loss: every value sent is eventually received.                 *)
NoDataLoss ==
    \A n \in Nat : (Len(sent) >= n) ~> (Len(rcvd) >= n)

(* A pending value is eventually acknowledged.                            *)
PendingEventuallyAcked ==
    (rdy # ack) ~> (rdy = ack)

(* Progress: the system keeps transferring data forever.                  *)
Progress ==
    /\ []<><<Send>>_vars
    /\ []<><<Rcv>>_vars

---------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Alternation
THEOREM Spec => NoDataLoss /\ PendingEventuallyAcked /\ Progress
=============================================================================
---------------------------- MODULE InnerFIFO ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

vars == <<in, out, q>>

-----------------------------------------------------------------------------
(* Channel record type: value, ready bit and acknowledgment bit            *)
ChanType == [val : Message, rdy : {0, 1}, ack : {0, 1}]

(* Generic channel type invariant and initial predicate                    *)
InChanTypeInvariant  == in  \in ChanType
OutChanTypeInvariant == out \in ChanType

InChanInit  == /\ in  \in ChanType
               /\ in.ack = in.rdy

OutChanInit == /\ out \in ChanType
               /\ out.ack = out.rdy

(* Two-phase handshake on the input channel                               *)
InChanSend(d) == /\ in.rdy = in.ack
                 /\ in' = [in EXCEPT !.val = d, !.rdy = 1 - @]

InChanRcv     == /\ in.rdy # in.ack
                 /\ in' = [in EXCEPT !.ack = 1 - @]

(* Two-phase handshake on the output channel                              *)
OutChanSend(d) == /\ out.rdy = out.ack
                  /\ out' = [out EXCEPT !.val = d, !.rdy = 1 - @]

OutChanRcv     == /\ out.rdy # out.ack
                  /\ out' = [out EXCEPT !.ack = 1 - @]

-----------------------------------------------------------------------------
TypeInvariant == /\ InChanTypeInvariant
                 /\ OutChanTypeInvariant
                 /\ q \in Seq(Message)

Init == /\ InChanInit
        /\ OutChanInit
        /\ q = << >>

-----------------------------------------------------------------------------
(* Sender sends a message msg on the input channel                         *)
SSend(msg) == /\ InChanSend(msg)
              /\ UNCHANGED <<out, q>>

(* Buffer receives a message from the input channel, appends it to q       *)
BufRcv == /\ InChanRcv
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out

(* Buffer sends the head of q on the output channel                        *)
BufSend == /\ q # << >>
           /\ OutChanSend(Head(q))
           /\ q' = Tail(q)
           /\ UNCHANGED in

(* Receiver receives a message from the output channel                     *)
RRcv == /\ OutChanRcv
        /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
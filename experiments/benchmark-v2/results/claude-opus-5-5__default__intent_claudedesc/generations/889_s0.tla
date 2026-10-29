---------------------------- MODULE AsyncChannel ----------------------------
EXTENDS Naturals

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLES chan, lastRcvd

vars == <<chan, lastRcvd>>

ChanType == [val : Data, rdy : {0, 1}, ack : {0, 1}]

TypeInvariant ==
    /\ chan \in ChanType
    /\ lastRcvd \in Data

-----------------------------------------------------------------------------

Init ==
    /\ chan \in ChanType
    /\ chan.rdy = chan.ack
    /\ lastRcvd = chan.val

Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]
    /\ UNCHANGED lastRcvd

Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]
    /\ lastRcvd' = chan.val

Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_vars /\ WF_vars(Rcv)

-----------------------------------------------------------------------------

InTransit == chan.rdy # chan.ack

NoDataLossInv ==
    (~InTransit) => (lastRcvd = chan.val)

DataStableWhileInTransit ==
    [][InTransit => (chan.val' = chan.val)]_vars

NoDuplication ==
    [][(chan.ack' # chan.ack) => InTransit]_vars

ReceiveOnlyOnAck ==
    [][(lastRcvd' # lastRcvd) => (chan.ack' # chan.ack)]_vars

ProtocolIntegrity ==
    [][ /\ (chan.rdy' # chan.rdy) =>
              (/\ chan.rdy = chan.ack
               /\ chan.ack' = chan.ack)
        /\ (chan.ack' # chan.ack) =>
              (/\ chan.rdy # chan.ack
               /\ chan.rdy' = chan.rdy)
        /\ (chan.val' # chan.val) => (chan.rdy' # chan.rdy)
      ]_vars

EventualDelivery ==
    \A d \in Data :
        (InTransit /\ chan.val = d) ~> (~InTransit /\ lastRcvd = d)

AckFollowsReady == InTransit ~> ~InTransit

-----------------------------------------------------------------------------

THEOREM Spec => [](TypeInvariant /\ NoDataLossInv)
THEOREM Spec => DataStableWhileInTransit /\ NoDuplication /\ ProtocolIntegrity
THEOREM Spec => EventualDelivery /\ AckFollowsReady

=============================================================================
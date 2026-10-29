---------------------------- MODULE tcp ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Peers

ASSUME Cardinality(Peers) = 2

VARIABLES tcb, connstate, network

vars == <<tcb, connstate, network>>

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "CLOSE-WAIT",
           "LAST-ACK", "TIME-WAIT"}

Messages == {"SYN", "SYNACK", "ACK", "FIN", "RST"}

Cap == 2

Other(p) == CHOOSE q \in Peers : q # p

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

Go(l, st) ==
    /\ connstate' = [connstate EXCEPT ![l] = st]
    /\ tcb' = [tcb EXCEPT ![l] = (st # "CLOSED")]

Stay == UNCHANGED <<connstate, tcb>>

Send(r, m) == network' = [network EXCEPT ![r] = Append(@, m)]

Consume(l) == network' = [network EXCEPT ![l] = Tail(@)]

ConsumeSend(l, r, m) ==
    network' = [network EXCEPT ![l] = Tail(@), ![r] = Append(@, m)]

Drop(l) == Consume(l) /\ Stay

CanSend(r) == Len(network[r]) < Cap

----------------------------------------------------------------------------
\* User commands

PASSIVE_OPEN(l, r) ==
    /\ connstate[l] = "CLOSED"
    /\ Go(l, "LISTEN")
    /\ UNCHANGED network

ACTIVE_OPEN(l, r) ==
    /\ connstate[l] = "CLOSED"
    /\ CanSend(r)
    /\ Go(l, "SYN-SENT")
    /\ Send(r, "SYN")

SEND(l, r) ==
    /\ connstate[l] = "LISTEN"
    /\ CanSend(r)
    /\ Go(l, "SYN-SENT")
    /\ Send(r, "SYN")

CLOSE(l, r) ==
    \/ /\ connstate[l] \in {"LISTEN", "SYN-SENT"}
       /\ Go(l, "CLOSED")
       /\ UNCHANGED network
    \/ /\ connstate[l] \in {"SYN-RECEIVED", "ESTABLISHED"}
       /\ CanSend(r)
       /\ Go(l, "FIN-WAIT-1")
       /\ Send(r, "FIN")
    \/ /\ connstate[l] = "CLOSE-WAIT"
       /\ CanSend(r)
       /\ Go(l, "LAST-ACK")
       /\ Send(r, "FIN")

ABORT(l, r) ==
    /\ connstate[l] \in {"SYN-RECEIVED", "ESTABLISHED", "FIN-WAIT-1",
                         "FIN-WAIT-2", "CLOSE-WAIT"}
    /\ CanSend(r)
    /\ Go(l, "TIME-WAIT")
    /\ Send(r, "RST")

User(l, r) ==
    \/ PASSIVE_OPEN(l, r)
    \/ ACTIVE_OPEN(l, r)
    \/ SEND(l, r)
    \/ CLOSE(l, r)
    \/ ABORT(l, r)

TIMEOUT(l) ==
    /\ connstate[l] = "TIME-WAIT"
    /\ Go(l, "CLOSED")
    /\ UNCHANGED network

----------------------------------------------------------------------------
\* Message receipt, per state

RcvClosed(l, r, m) ==
    IF m = "RST"
    THEN Drop(l)
    ELSE ConsumeSend(l, r, "RST") /\ Stay

RcvListen(l, r, m) ==
    CASE m = "SYN" -> Go(l, "SYN-RECEIVED") /\ ConsumeSend(l, r, "SYNACK")
      [] m \in {"ACK", "SYNACK"} -> ConsumeSend(l, r, "RST") /\ Stay
      [] OTHER -> Drop(l)

RcvSynSent(l, r, m) ==
    CASE m = "SYNACK" -> Go(l, "ESTABLISHED") /\ ConsumeSend(l, r, "ACK")
      [] m = "SYN" -> Go(l, "SYN-RECEIVED") /\ ConsumeSend(l, r, "SYNACK")
      [] m = "RST" -> Go(l, "CLOSED") /\ Consume(l)
      [] OTHER -> Drop(l)

RcvSynRcvd(l, r, m) ==
    CASE m \in {"ACK", "SYNACK"} -> Go(l, "ESTABLISHED") /\ Consume(l)
      [] m = "RST" -> Go(l, "LISTEN") /\ Consume(l)
      [] m = "FIN" -> Go(l, "CLOSE-WAIT") /\ ConsumeSend(l, r, "ACK")
      [] OTHER -> Drop(l)

RcvEstablished(l, r, m) ==
    CASE m = "FIN" -> Go(l, "CLOSE-WAIT") /\ ConsumeSend(l, r, "ACK")
      [] m = "RST" -> Go(l, "CLOSED") /\ Consume(l)
      [] OTHER -> Drop(l)

RcvFinWait1(l, r, m) ==
    CASE m \in {"ACK", "SYNACK"} -> Go(l, "FIN-WAIT-2") /\ Consume(l)
      [] m = "FIN" -> Go(l, "CLOSING") /\ ConsumeSend(l, r, "ACK")
      [] m = "RST" -> Go(l, "CLOSED") /\ Consume(l)
      [] OTHER -> Drop(l)

RcvFinWait2(l, r, m) ==
    CASE m = "FIN" -> Go(l, "TIME-WAIT") /\ ConsumeSend(l, r, "ACK")
      [] m = "RST" -> Go(l, "CLOSED") /\ Consume(l)
      [] OTHER -> Drop(l)

RcvClosing(l, r, m) ==
    CASE m = "ACK" -> Go(l, "TIME-WAIT") /\ Consume(l)
      [] m = "RST" -> Go(l, "CLOSED") /\ Consume(l)
      [] OTHER -> Drop(l)

RcvCloseWait(l, r, m) ==
    IF m = "RST"
    THEN Go(l, "CLOSED") /\ Consume(l)
    ELSE Drop(l)

RcvLastAck(l, r, m) ==
    IF m \in {"ACK", "RST"}
    THEN Go(l, "CLOSED") /\ Consume(l)
    ELSE Drop(l)

RcvTimeWait(l, r, m) ==
    IF m = "RST"
    THEN Go(l, "CLOSED") /\ Consume(l)
    ELSE Drop(l)

Receive(l, r) ==
    /\ network[l] # <<>>
    /\ LET m == Head(network[l])
           s == connstate[l]
       IN  CASE s = "CLOSED"       -> RcvClosed(l, r, m)
             [] s = "LISTEN"       -> RcvListen(l, r, m)
             [] s = "SYN-SENT"     -> RcvSynSent(l, r, m)
             [] s = "SYN-RECEIVED" -> RcvSynRcvd(l, r, m)
             [] s = "ESTABLISHED"  -> RcvEstablished(l, r, m)
             [] s = "FIN-WAIT-1"   -> RcvFinWait1(l, r, m)
             [] s = "FIN-WAIT-2"   -> RcvFinWait2(l, r, m)
             [] s = "CLOSING"      -> RcvClosing(l, r, m)
             [] s = "CLOSE-WAIT"   -> RcvCloseWait(l, r, m)
             [] s = "LAST-ACK"     -> RcvLastAck(l, r, m)
             [] s = "TIME-WAIT"    -> RcvTimeWait(l, r, m)

----------------------------------------------------------------------------

Next ==
    \E l \in Peers :
        \/ User(l, Other(l))
        \/ Receive(l, Other(l))
        \/ TIMEOUT(l)

Fairness ==
    \A p \in Peers :
        /\ WF_vars(Receive(p, Other(p)))
        /\ WF_vars(TIMEOUT(p))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Properties

Inv ==
    (\A p \in Peers : network[p] = <<>>) =>
        \A p, q \in Peers :
            connstate[p] = "ESTABLISHED" => connstate[q] = "ESTABLISHED"

Prop ==
    \A p \in Peers :
        /\ (connstate[p] = "SYN-SENT") ~>
               (connstate[p] \in {"ESTABLISHED", "CLOSED", "LISTEN"})
        /\ (connstate[p] = "TIME-WAIT") ~>
               (connstate[p] = "CLOSED" /\ ~tcb[p])

=============================================================================
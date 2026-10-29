------------------------------- MODULE tcp -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Peers

ASSUME Cardinality(Peers) = 2

States == { "CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
            "FIN-WAIT-1", "FIN-WAIT-2", "CLOSE-WAIT", "CLOSING",
            "LAST-ACK", "TIME-WAIT" }

Messages == { "SYN", "SYN,ACK", "ACK", "FIN", "RST" }

VARIABLES
    tcb,        \* tcb[p] : does peer p have a TCP control block?
    connstate,  \* connstate[p] : current connection state of peer p
    network     \* network[p] : sequence of in-flight messages destined to p

vars == << tcb, connstate, network >>

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> << >>]

---------------------------------------------------------------------------
(* Helpers *)

\* p sends message m to q
SendMsg(p, q, m) == network' = [network EXCEPT ![q] = Append(@, m)]

\* p consumes the head of its inbox
Drop(p) == network' = [network EXCEPT ![p] = Tail(@)]

\* p consumes head of its inbox and sends m to q
RcvSend(p, q, m) ==
    network' = [network EXCEPT ![p] = Tail(@), ![q] = Append(@, m)]

HasMsg(p, m) == network[p] /= << >> /\ Head(network[p]) = m

---------------------------------------------------------------------------
(* User actions *)

PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "LISTEN"]
    /\ UNCHANGED network

ActiveOpen(p, q) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendMsg(p, q, "SYN")

\* SEND call in LISTEN: turn passive into active open
SendCall(p, q) ==
    /\ connstate[p] = "LISTEN"
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendMsg(p, q, "SYN")
    /\ UNCHANGED tcb

CloseListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

\* Close in SYN-SENT; given weak fairness to avoid getting stuck in SYN-SENT
CloseSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

CloseSynRcvdOrEstablished(p, q) ==
    /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
    /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-1"]
    /\ SendMsg(p, q, "FIN")
    /\ UNCHANGED tcb

CloseCloseWait(p, q) ==
    /\ connstate[p] = "CLOSE-WAIT"
    /\ connstate' = [connstate EXCEPT ![p] = "LAST-ACK"]
    /\ SendMsg(p, q, "FIN")
    /\ UNCHANGED tcb

Close(p, q) ==
    \/ CloseListen(p)
    \/ CloseSynSent(p)
    \/ CloseSynRcvdOrEstablished(p, q)
    \/ CloseCloseWait(p, q)

\* ABORT / reset: applicable in any state with a TCB
Abort(p, q) ==
    /\ connstate[p] /= "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ IF connstate[p] \in {"LISTEN", "SYN-SENT"}
          THEN UNCHANGED network
          ELSE SendMsg(p, q, "RST")

User(p, q) ==
    \/ PassiveOpen(p)
    \/ ActiveOpen(p, q)
    \/ SendCall(p, q)
    \/ Close(p, q)
    \/ Abort(p, q)

---------------------------------------------------------------------------
(* System (protocol-driven) actions *)

ListenRcvSyn(p, q) ==
    /\ connstate[p] = "LISTEN"
    /\ HasMsg(p, "SYN")
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-RECEIVED"]
    /\ RcvSend(p, q, "SYN,ACK")
    /\ UNCHANGED tcb

SynSentRcvSynAck(p, q) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HasMsg(p, "SYN,ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "ESTABLISHED"]
    /\ RcvSend(p, q, "ACK")
    /\ UNCHANGED tcb

\* Simultaneous open
SynSentRcvSyn(p, q) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HasMsg(p, "SYN")
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-RECEIVED"]
    /\ RcvSend(p, q, "ACK")
    /\ UNCHANGED tcb

SynRcvdRcvAck(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ HasMsg(p, "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "ESTABLISHED"]
    /\ Drop(p)
    /\ UNCHANGED tcb

EstablishedRcvFin(p, q) ==
    /\ connstate[p] = "ESTABLISHED"
    /\ HasMsg(p, "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSE-WAIT"]
    /\ RcvSend(p, q, "ACK")
    /\ UNCHANGED tcb

FinWait1RcvAck(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasMsg(p, "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-2"]
    /\ Drop(p)
    /\ UNCHANGED tcb

FinWait1RcvFin(p, q) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasMsg(p, "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSING"]
    /\ RcvSend(p, q, "ACK")
    /\ UNCHANGED tcb

\* RFC note: FIN-WAIT-1 may go directly to TIME-WAIT on receiving FIN
\* whose segment also acknowledges our FIN.
FinWait1ToTimeWait(p, q) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasMsg(p, "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ RcvSend(p, q, "ACK")
    /\ UNCHANGED tcb

FinWait2RcvFin(p, q) ==
    /\ connstate[p] = "FIN-WAIT-2"
    /\ HasMsg(p, "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ RcvSend(p, q, "ACK")
    /\ UNCHANGED tcb

ClosingRcvAck(p) ==
    /\ connstate[p] = "CLOSING"
    /\ HasMsg(p, "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ Drop(p)
    /\ UNCHANGED tcb

LastAckRcvAck(p) ==
    /\ connstate[p] = "LAST-ACK"
    /\ HasMsg(p, "ACK")
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ Drop(p)

TimeWaitTimeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

\* Receipt of a reset
RcvRst(p) ==
    /\ HasMsg(p, "RST")
    /\ IF connstate[p] \in {"CLOSED", "LISTEN"}
          THEN UNCHANGED << tcb, connstate >>
          ELSE /\ tcb' = [tcb EXCEPT ![p] = FALSE]
               /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ Drop(p)

\* A CLOSED peer discards any incoming (non-RST) segment
ClosedDrop(p) ==
    /\ connstate[p] = "CLOSED"
    /\ network[p] /= << >>
    /\ Head(network[p]) /= "RST"
    /\ Drop(p)
    /\ UNCHANGED << tcb, connstate >>

System(p, q) ==
    \/ ListenRcvSyn(p, q)
    \/ SynSentRcvSynAck(p, q)
    \/ SynSentRcvSyn(p, q)
    \/ SynRcvdRcvAck(p)
    \/ EstablishedRcvFin(p, q)
    \/ FinWait1RcvAck(p)
    \/ FinWait1RcvFin(p, q)
    \/ FinWait1ToTimeWait(p, q)
    \/ FinWait2RcvFin(p, q)
    \/ ClosingRcvAck(p)
    \/ LastAckRcvAck(p)
    \/ TimeWaitTimeout(p)
    \/ RcvRst(p)
    \/ ClosedDrop(p)

---------------------------------------------------------------------------

Next ==
    \E p, q \in Peers :
        /\ p /= q
        /\ \/ User(p, q)
           \/ System(p, q)

Fairness ==
    /\ WF_vars(\E p, q \in Peers : p /= q /\ System(p, q))
    /\ \A p \in Peers : WF_vars(CloseSynSent(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Properties *)

\* When no messages are in flight, peers agree on being ESTABLISHED.
Inv ==
    (\A p \in Peers : network[p] = << >>) =>
        \A p, q \in Peers :
            (connstate[p] = "ESTABLISHED") <=> (connstate[q] = "ESTABLISHED")

\* A peer in SYN-SENT eventually reaches ESTABLISHED, LISTEN, or CLOSED.
SynSentLeadsTo ==
    \A p \in Peers :
        (connstate[p] = "SYN-SENT") ~>
            (connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"})

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => SynSentLeadsTo
===========================================================================
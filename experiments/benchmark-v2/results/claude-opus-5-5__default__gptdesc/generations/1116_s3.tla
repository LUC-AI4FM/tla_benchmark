------------------------------- MODULE TCP -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Peers

ASSUME Cardinality(Peers) = 2

VARIABLES
    tcb,        \* tcb[p] : TRUE iff peer p currently has a TCP control block
    connstate,  \* connstate[p] : current RFC 9293 connection state of peer p
    network     \* network[p] : sequence of in-flight messages destined to p

vars == << tcb, connstate, network >>

States == { "CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
            "FIN-WAIT-1", "FIN-WAIT-2", "CLOSE-WAIT", "CLOSING",
            "LAST-ACK", "TIME-WAIT" }

Messages == { "SYN", "SYN,ACK", "ACK", "FIN", "RST" }

Other(p) == CHOOSE q \in Peers : q # p

---------------------------------------------------------------------------
\* Helpers

\* Send message m from p to its peer
SendMsg(p, m) ==
    network' = [network EXCEPT ![Other(p)] = Append(@, m)]

\* Consume the head of p's inbound queue, without replying
Consume(p) ==
    network' = [network EXCEPT ![p] = Tail(@)]

\* Consume the head of p's inbound queue and reply with message m
ConsumeAndSend(p, m) ==
    network' = [network EXCEPT ![p] = Tail(@), ![Other(p)] = Append(@, m)]

\* Peer p is in state s and the next inbound message is m
Rcv(p, s, m) ==
    /\ connstate[p] = s
    /\ network[p] # << >>
    /\ Head(network[p]) = m

\* Messages a peer in a given state is prepared to process
Expected(s, m) ==
    \/ s = "LISTEN"       /\ m \in {"SYN"}
    \/ s = "SYN-SENT"     /\ m \in {"SYN,ACK", "SYN", "RST"}
    \/ s = "SYN-RECEIVED" /\ m \in {"ACK", "SYN,ACK", "RST"}
    \/ s = "ESTABLISHED"  /\ m \in {"FIN", "RST"}
    \/ s = "FIN-WAIT-1"   /\ m \in {"ACK", "FIN", "RST"}
    \/ s = "FIN-WAIT-2"   /\ m \in {"FIN", "RST"}
    \/ s = "CLOSE-WAIT"   /\ m \in {"RST"}
    \/ s = "CLOSING"      /\ m \in {"ACK", "RST"}
    \/ s = "LAST-ACK"     /\ m \in {"ACK", "RST"}
    \/ s = "TIME-WAIT"    /\ m \in {"RST"}

---------------------------------------------------------------------------
TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> << >>]

---------------------------------------------------------------------------
\* User-triggered actions

PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "LISTEN"]
    /\ UNCHANGED network

ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendMsg(p, "SYN")

\* SEND call in LISTEN: switch to active open
SendFromListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendMsg(p, "SYN")
    /\ UNCHANGED tcb

CloseListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

CloseSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

CloseSynRcvdOrEstablished(p) ==
    /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
    /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-1"]
    /\ SendMsg(p, "FIN")
    /\ UNCHANGED tcb

CloseCloseWait(p) ==
    /\ connstate[p] = "CLOSE-WAIT"
    /\ connstate' = [connstate EXCEPT ![p] = "LAST-ACK"]
    /\ SendMsg(p, "FIN")
    /\ UNCHANGED tcb

\* ABORT call: delete the TCB, sending RST where RFC 9293 requires it
Abort(p) ==
    /\ connstate[p] \notin {"CLOSED"}
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ IF connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED", "FIN-WAIT-1",
                            "FIN-WAIT-2", "CLOSE-WAIT"}
          THEN SendMsg(p, "RST")
          ELSE UNCHANGED network

UserAction(p) ==
    \/ PassiveOpen(p)
    \/ ActiveOpen(p)
    \/ SendFromListen(p)
    \/ CloseListen(p)
    \/ CloseSynSent(p)
    \/ CloseSynRcvdOrEstablished(p)
    \/ CloseCloseWait(p)
    \/ Abort(p)

---------------------------------------------------------------------------
\* Protocol-driven transitions

ListenRcvSyn(p) ==
    /\ Rcv(p, "LISTEN", "SYN")
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-RECEIVED"]
    /\ ConsumeAndSend(p, "SYN,ACK")
    /\ UNCHANGED tcb

SynSentRcvSynAck(p) ==
    /\ Rcv(p, "SYN-SENT", "SYN,ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "ESTABLISHED"]
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

\* Simultaneous open
SynSentRcvSyn(p) ==
    /\ Rcv(p, "SYN-SENT", "SYN")
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-RECEIVED"]
    /\ ConsumeAndSend(p, "SYN,ACK")
    /\ UNCHANGED tcb

SynRcvdRcvAck(p) ==
    /\ Rcv(p, "SYN-RECEIVED", "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "ESTABLISHED"]
    /\ Consume(p)
    /\ UNCHANGED tcb

SynRcvdRcvSynAck(p) ==
    /\ Rcv(p, "SYN-RECEIVED", "SYN,ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "ESTABLISHED"]
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

EstablishedRcvFin(p) ==
    /\ Rcv(p, "ESTABLISHED", "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSE-WAIT"]
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

FinWait1RcvAck(p) ==
    /\ Rcv(p, "FIN-WAIT-1", "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-2"]
    /\ Consume(p)
    /\ UNCHANGED tcb

FinWait1RcvFin(p) ==
    /\ Rcv(p, "FIN-WAIT-1", "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSING"]
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

\* RFC note: FIN-WAIT-1 directly to TIME-WAIT when the received FIN
\* also acknowledges our FIN
FinWait1ToTimeWait(p) ==
    /\ Rcv(p, "FIN-WAIT-1", "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

FinWait2RcvFin(p) ==
    /\ Rcv(p, "FIN-WAIT-2", "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

ClosingRcvAck(p) ==
    /\ Rcv(p, "CLOSING", "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ Consume(p)
    /\ UNCHANGED tcb

LastAckRcvAck(p) ==
    /\ Rcv(p, "LAST-ACK", "ACK")
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ Consume(p)

TimeWaitTimeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

\* Reset: receiving RST in any state with a live connection
RcvReset(p) ==
    /\ connstate[p] \notin {"CLOSED", "LISTEN"}
    /\ network[p] # << >>
    /\ Head(network[p]) = "RST"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ Consume(p)

\* Discard messages that are not meaningful in the current state
DropUnexpected(p) ==
    /\ network[p] # << >>
    /\ ~Expected(connstate[p], Head(network[p]))
    /\ Consume(p)
    /\ UNCHANGED << tcb, connstate >>

SystemStep(p) ==
    \/ ListenRcvSyn(p)
    \/ SynSentRcvSynAck(p)
    \/ SynSentRcvSyn(p)
    \/ SynRcvdRcvAck(p)
    \/ SynRcvdRcvSynAck(p)
    \/ EstablishedRcvFin(p)
    \/ FinWait1RcvAck(p)
    \/ FinWait1RcvFin(p)
    \/ FinWait1ToTimeWait(p)
    \/ FinWait2RcvFin(p)
    \/ ClosingRcvAck(p)
    \/ LastAckRcvAck(p)
    \/ TimeWaitTimeout(p)
    \/ RcvReset(p)
    \/ DropUnexpected(p)

---------------------------------------------------------------------------
Next ==
    \E p \in Peers :
        \/ UserAction(p)
        \/ SystemStep(p)

Fairness ==
    /\ \A p \in Peers : WF_vars(SystemStep(p))
    /\ \A p \in Peers : WF_vars(CloseSynSent(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
\* Properties

TCBConsistent ==
    \A p \in Peers : tcb[p] <=> (connstate[p] # "CLOSED")

\* When no messages are in flight, both peers agree on being ESTABLISHED
EstablishedAgreement ==
    \A p, q \in Peers :
        (network[p] = << >> /\ network[q] = << >>)
            => (connstate[p] = "ESTABLISHED" <=> connstate[q] = "ESTABLISHED")

Inv == TypeOK /\ EstablishedAgreement

\* A peer in SYN-SENT eventually reaches ESTABLISHED, LISTEN, or CLOSED
SynSentLeadsTo ==
    \A p \in Peers :
        (connstate[p] = "SYN-SENT")
            ~> (connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"})

THEOREM Spec => [](TypeOK /\ EstablishedAgreement)
THEOREM Spec => SynSentLeadsTo
===========================================================================
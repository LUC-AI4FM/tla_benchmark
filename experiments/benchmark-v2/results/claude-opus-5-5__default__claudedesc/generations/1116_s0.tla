------------------------------- MODULE tcp -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Peers

ASSUME Cardinality(Peers) = 2

VARIABLES tcb, connstate, network

vars == <<tcb, connstate, network>>

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "CLOSE-WAIT",
           "LAST-ACK", "TIME-WAIT"}

Segments == {"SYN", "SYN-ACK", "ACK", "RST", "FIN", "ACKofFIN"}

Other(p) == CHOOSE q \in Peers : q # p

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Segments)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

\* Helpers
Send(remote, seg) == [network EXCEPT ![remote] = Append(@, seg)]

Recv(local, seg) ==
    /\ network[local] # <<>>
    /\ Head(network[local]) = seg

\* Consume the head segment for local and append seg to the queue of remote
RecvSend(local, remote, seg) ==
    [network EXCEPT ![local] = Tail(@), ![remote] = Append(@, seg)]

Consume(local) == [network EXCEPT ![local] = Tail(@)]

SetState(p, s) == connstate' = [connstate EXCEPT ![p] = s]

---------------------------------------------------------------------------
\* User actions

PassiveOpen(local, remote) ==
    /\ connstate[local] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![local] = TRUE]
    /\ SetState(local, "LISTEN")
    /\ UNCHANGED network

ActiveOpen(local, remote) ==
    /\ connstate[local] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![local] = TRUE]
    /\ SetState(local, "SYN-SENT")
    /\ network' = Send(remote, "SYN")

SendListen(local, remote) ==
    /\ connstate[local] = "LISTEN"
    /\ SetState(local, "SYN-SENT")
    /\ network' = Send(remote, "SYN")
    /\ UNCHANGED tcb

CloseListen(local, remote) ==
    /\ connstate[local] = "LISTEN"
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    /\ SetState(local, "CLOSED")
    /\ UNCHANGED network

CloseSynSent(local, remote) ==
    /\ connstate[local] = "SYN-SENT"
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    /\ SetState(local, "CLOSED")
    /\ UNCHANGED network

CloseSynReceived(local, remote) ==
    /\ connstate[local] = "SYN-RECEIVED"
    /\ SetState(local, "FIN-WAIT-1")
    /\ network' = Send(remote, "FIN")
    /\ UNCHANGED tcb

CloseEstablished(local, remote) ==
    /\ connstate[local] = "ESTABLISHED"
    /\ SetState(local, "FIN-WAIT-1")
    /\ network' = Send(remote, "FIN")
    /\ UNCHANGED tcb

CloseCloseWait(local, remote) ==
    /\ connstate[local] = "CLOSE-WAIT"
    /\ SetState(local, "LAST-ACK")
    /\ network' = Send(remote, "FIN")
    /\ UNCHANGED tcb

User(local, remote) ==
    \/ PassiveOpen(local, remote)
    \/ ActiveOpen(local, remote)
    \/ SendListen(local, remote)
    \/ CloseListen(local, remote)
    \/ CloseSynSent(local, remote)
    \/ CloseSynReceived(local, remote)
    \/ CloseEstablished(local, remote)
    \/ CloseCloseWait(local, remote)

---------------------------------------------------------------------------
\* System actions (segment arrival and timeouts)

ListenSyn(local, remote) ==
    /\ connstate[local] = "LISTEN"
    /\ Recv(local, "SYN")
    /\ SetState(local, "SYN-RECEIVED")
    /\ network' = RecvSend(local, remote, "SYN-ACK")
    /\ UNCHANGED tcb

SynSentSynAck(local, remote) ==
    /\ connstate[local] = "SYN-SENT"
    /\ Recv(local, "SYN-ACK")
    /\ SetState(local, "ESTABLISHED")
    /\ network' = RecvSend(local, remote, "ACK")
    /\ UNCHANGED tcb

SynSentSyn(local, remote) ==   \* simultaneous open
    /\ connstate[local] = "SYN-SENT"
    /\ Recv(local, "SYN")
    /\ SetState(local, "SYN-RECEIVED")
    /\ network' = RecvSend(local, remote, "SYN-ACK")
    /\ UNCHANGED tcb

SynReceivedAck(local, remote) ==
    /\ connstate[local] = "SYN-RECEIVED"
    /\ network[local] # <<>>
    /\ Head(network[local]) \in {"ACK", "SYN-ACK"}
    /\ SetState(local, "ESTABLISHED")
    /\ network' = Consume(local)
    /\ UNCHANGED tcb

EstablishedFin(local, remote) ==
    /\ connstate[local] = "ESTABLISHED"
    /\ Recv(local, "FIN")
    /\ SetState(local, "CLOSE-WAIT")
    /\ network' = RecvSend(local, remote, "ACKofFIN")
    /\ UNCHANGED tcb

FinWait1Fin(local, remote) ==
    /\ connstate[local] = "FIN-WAIT-1"
    /\ Recv(local, "FIN")
    /\ SetState(local, "CLOSING")
    /\ network' = RecvSend(local, remote, "ACKofFIN")
    /\ UNCHANGED tcb

FinWait1AckOfFin(local, remote) ==
    /\ connstate[local] = "FIN-WAIT-1"
    /\ Recv(local, "ACKofFIN")
    /\ SetState(local, "FIN-WAIT-2")
    /\ network' = Consume(local)
    /\ UNCHANGED tcb

FinWait2Fin(local, remote) ==
    /\ connstate[local] = "FIN-WAIT-2"
    /\ Recv(local, "FIN")
    /\ SetState(local, "TIME-WAIT")
    /\ network' = RecvSend(local, remote, "ACKofFIN")
    /\ UNCHANGED tcb

ClosingAckOfFin(local, remote) ==
    /\ connstate[local] = "CLOSING"
    /\ Recv(local, "ACKofFIN")
    /\ SetState(local, "TIME-WAIT")
    /\ network' = Consume(local)
    /\ UNCHANGED tcb

LastAckAckOfFin(local, remote) ==
    /\ connstate[local] = "LAST-ACK"
    /\ Recv(local, "ACKofFIN")
    /\ SetState(local, "CLOSED")
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    /\ network' = Consume(local)

TimeWaitTimeout(local, remote) ==
    /\ connstate[local] = "TIME-WAIT"
    /\ SetState(local, "CLOSED")
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    /\ UNCHANGED network

\* A CLOSED peer answers any non-RST segment with RST and drops RSTs.
ClosedRecv(local, remote) ==
    /\ connstate[local] = "CLOSED"
    /\ network[local] # <<>>
    /\ IF Head(network[local]) = "RST"
         THEN network' = Consume(local)
         ELSE network' = RecvSend(local, remote, "RST")
    /\ UNCHANGED <<tcb, connstate>>

Handled(s, seg) ==
    \/ s = "CLOSED"
    \/ s = "LISTEN"       /\ seg = "SYN"
    \/ s = "SYN-SENT"     /\ seg \in {"SYN-ACK", "SYN", "RST"}
    \/ s = "SYN-RECEIVED" /\ seg \in {"ACK", "SYN-ACK", "RST"}
    \/ s = "ESTABLISHED"  /\ seg \in {"FIN", "RST"}
    \/ s = "FIN-WAIT-1"   /\ seg \in {"FIN", "ACKofFIN", "RST"}
    \/ s = "FIN-WAIT-2"   /\ seg \in {"FIN", "RST"}
    \/ s = "CLOSING"      /\ seg \in {"ACKofFIN", "RST"}
    \/ s = "CLOSE-WAIT"   /\ seg = "RST"
    \/ s = "LAST-ACK"     /\ seg \in {"ACKofFIN", "RST"}
    \/ s = "TIME-WAIT"    /\ seg = "RST"

\* Segments that are not meaningful in the current state are discarded.
DropUnexpected(local, remote) ==
    /\ network[local] # <<>>
    /\ ~Handled(connstate[local], Head(network[local]))
    /\ network' = Consume(local)
    /\ UNCHANGED <<tcb, connstate>>

System(local, remote) ==
    \/ ListenSyn(local, remote)
    \/ SynSentSynAck(local, remote)
    \/ SynSentSyn(local, remote)
    \/ SynReceivedAck(local, remote)
    \/ EstablishedFin(local, remote)
    \/ FinWait1Fin(local, remote)
    \/ FinWait1AckOfFin(local, remote)
    \/ FinWait2Fin(local, remote)
    \/ ClosingAckOfFin(local, remote)
    \/ LastAckAckOfFin(local, remote)
    \/ TimeWaitTimeout(local, remote)
    \/ ClosedRecv(local, remote)
    \/ DropUnexpected(local, remote)

---------------------------------------------------------------------------
\* RST handling (RFC 9293, note 3): a reset in SYN-RECEIVED returns the
\* connection to LISTEN; in any other synchronized/opening state the
\* connection is aborted and goes to CLOSED.
Reset(local, remote) ==
    /\ connstate[local] \notin {"CLOSED", "LISTEN"}
    /\ Recv(local, "RST")
    /\ network' = Consume(local)
    /\ IF connstate[local] = "SYN-RECEIVED"
         THEN /\ SetState(local, "LISTEN")
              /\ UNCHANGED tcb
         ELSE /\ SetState(local, "CLOSED")
              /\ tcb' = [tcb EXCEPT ![local] = FALSE]

---------------------------------------------------------------------------
Next ==
    \E local \in Peers :
        LET remote == Other(local) IN
            \/ User(local, remote)
            \/ System(local, remote)
            \/ Reset(local, remote)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Peers : WF_vars(System(p, Other(p)))
    /\ \A p \in Peers : WF_vars(CloseSynSent(p, Other(p)))

---------------------------------------------------------------------------
\* Properties

\* When no segments are in flight, the peers agree on being ESTABLISHED.
Inv ==
    (\A p \in Peers : network[p] = <<>>) =>
        \A p, q \in Peers :
            (connstate[p] = "ESTABLISHED") <=> (connstate[q] = "ESTABLISHED")

\* A peer in SYN-SENT eventually becomes ESTABLISHED, LISTEN, or CLOSED.
Prop ==
    \A p \in Peers :
        connstate[p] = "SYN-SENT" ~>
            connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Prop
===========================================================================
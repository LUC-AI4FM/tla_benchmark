------------------------------- MODULE tcp -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT peers

ASSUME Cardinality(peers) = 2

States == {"LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSE-WAIT", "CLOSING",
           "LAST-ACK", "TIME-WAIT", "CLOSED"}

Messages == {"SYN", "SYN,ACK", "ACK", "RST", "FIN"}

VARIABLES
    tcb,        \* tcb[p]: whether peer p currently has a TCP control block
    connstate,  \* connstate[p]: current connection state of peer p
    network     \* network[p]: sequence of in-flight messages destined for p

vars == <<tcb, connstate, network>>

Other(p) == CHOOSE q \in peers : q # p

TypeOK ==
    /\ tcb \in [peers -> BOOLEAN]
    /\ connstate \in [peers -> States]
    /\ network \in [peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in peers |-> FALSE]
    /\ connstate = [p \in peers |-> "CLOSED"]
    /\ network = [p \in peers |-> <<>>]

(* ---------------------------- Helpers ---------------------------------- *)

HasMsg(p, m) == Len(network[p]) > 0 /\ Head(network[p]) = m

\* Consume the head message at p and send msg to the other peer
ConsumeAndSend(p, msg) ==
    network' = [network EXCEPT ![p] = Tail(network[p]),
                               ![Other(p)] = Append(network[Other(p)], msg)]

Consume(p) ==
    network' = [network EXCEPT ![p] = Tail(network[p])]

Send(p, msg) ==
    network' = [network EXCEPT ![Other(p)] = Append(network[Other(p)], msg)]

SetState(p, s) == connstate' = [connstate EXCEPT ![p] = s]

(* ---------------------------- User actions ----------------------------- *)

PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ SetState(p, "LISTEN")
    /\ UNCHANGED network

ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ SetState(p, "SYN-SENT")
    /\ Send(p, "SYN")

SendFromListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ SetState(p, "SYN-SENT")
    /\ Send(p, "SYN")
    /\ UNCHANGED tcb

CloseListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ UNCHANGED network

CloseSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ UNCHANGED network

CloseSynReceivedOrEstablished(p) ==
    /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
    /\ SetState(p, "FIN-WAIT-1")
    /\ Send(p, "FIN")
    /\ UNCHANGED tcb

CloseCloseWait(p) ==
    /\ connstate[p] = "CLOSE-WAIT"
    /\ SetState(p, "LAST-ACK")
    /\ Send(p, "FIN")
    /\ UNCHANGED tcb

\* Abort / reset: applicable in any state except CLOSED
Reset(p) ==
    /\ connstate[p] # "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ Send(p, "RST")

User(p) ==
    \/ PassiveOpen(p)
    \/ ActiveOpen(p)
    \/ SendFromListen(p)
    \/ CloseListen(p)
    \/ CloseSynSent(p)
    \/ CloseSynReceivedOrEstablished(p)
    \/ CloseCloseWait(p)
    \/ Reset(p)

(* --------------------------- System actions ---------------------------- *)

ListenSyn(p) ==
    /\ connstate[p] = "LISTEN"
    /\ HasMsg(p, "SYN")
    /\ SetState(p, "SYN-RECEIVED")
    /\ ConsumeAndSend(p, "SYN,ACK")
    /\ UNCHANGED tcb

SynSentSynAck(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HasMsg(p, "SYN,ACK")
    /\ SetState(p, "ESTABLISHED")
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

\* Simultaneous open
SynSentSyn(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HasMsg(p, "SYN")
    /\ SetState(p, "SYN-RECEIVED")
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

SynReceivedAck(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ HasMsg(p, "ACK")
    /\ SetState(p, "ESTABLISHED")
    /\ Consume(p)
    /\ UNCHANGED tcb

EstablishedFin(p) ==
    /\ connstate[p] = "ESTABLISHED"
    /\ HasMsg(p, "FIN")
    /\ SetState(p, "CLOSE-WAIT")
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

FinWait1Ack(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasMsg(p, "ACK")
    /\ SetState(p, "FIN-WAIT-2")
    /\ Consume(p)
    /\ UNCHANGED tcb

FinWait1Fin(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasMsg(p, "FIN")
    /\ SetState(p, "CLOSING")
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

\* RFC note: FIN-WAIT-1 directly to TIME-WAIT when our FIN is ACKed
\* together with the peer's FIN.
FinWait1FinAckShortcut(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ Len(network[p]) >= 2
    /\ network[p][1] = "ACK"
    /\ network[p][2] = "FIN"
    /\ SetState(p, "TIME-WAIT")
    /\ network' = [network EXCEPT ![p] = SubSeq(network[p], 3, Len(network[p])),
                                  ![Other(p)] = Append(network[Other(p)], "ACK")]
    /\ UNCHANGED tcb

FinWait2Fin(p) ==
    /\ connstate[p] = "FIN-WAIT-2"
    /\ HasMsg(p, "FIN")
    /\ SetState(p, "TIME-WAIT")
    /\ ConsumeAndSend(p, "ACK")
    /\ UNCHANGED tcb

ClosingAck(p) ==
    /\ connstate[p] = "CLOSING"
    /\ HasMsg(p, "ACK")
    /\ SetState(p, "TIME-WAIT")
    /\ Consume(p)
    /\ UNCHANGED tcb

LastAckAck(p) ==
    /\ connstate[p] = "LAST-ACK"
    /\ HasMsg(p, "ACK")
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ Consume(p)

TimeWaitTimeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ UNCHANGED network

\* Receiving a reset
ReceiveRst(p) ==
    /\ HasMsg(p, "RST")
    /\ connstate[p] # "CLOSED"
    /\ IF connstate[p] = "LISTEN"
          THEN /\ UNCHANGED <<tcb, connstate>>
          ELSE /\ tcb' = [tcb EXCEPT ![p] = FALSE]
               /\ SetState(p, "CLOSED")
    /\ Consume(p)

\* A closed peer discards any incoming segment
ClosedDrop(p) ==
    /\ connstate[p] = "CLOSED"
    /\ Len(network[p]) > 0
    /\ Consume(p)
    /\ UNCHANGED <<tcb, connstate>>

System(p) ==
    \/ ListenSyn(p)
    \/ SynSentSynAck(p)
    \/ SynSentSyn(p)
    \/ SynReceivedAck(p)
    \/ EstablishedFin(p)
    \/ FinWait1Ack(p)
    \/ FinWait1Fin(p)
    \/ FinWait1FinAckShortcut(p)
    \/ FinWait2Fin(p)
    \/ ClosingAck(p)
    \/ LastAckAck(p)
    \/ TimeWaitTimeout(p)
    \/ ReceiveRst(p)
    \/ ClosedDrop(p)

(* ------------------------------ Spec ----------------------------------- *)

Next == \E p \in peers : User(p) \/ System(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in peers : System(p))
    /\ \A p \in peers : WF_vars(CloseSynSent(p))

(* ---------------------------- Properties ------------------------------- *)

\* When no messages are in flight, both peers agree on being ESTABLISHED.
Inv ==
    \A p, q \in peers :
        (network[p] = <<>> /\ network[q] = <<>>)
            => (connstate[p] = "ESTABLISHED" <=> connstate[q] = "ESTABLISHED")

\* A peer in SYN-SENT eventually reaches ESTABLISHED, LISTEN, or CLOSED.
SynSentLeadsTo ==
    \A p \in peers :
        connstate[p] = "SYN-SENT"
            ~> connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => SynSentLeadsTo
=============================================================================
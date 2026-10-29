--------------------------------- MODULE tcp ---------------------------------
(***************************************************************************)
(* Abstract two-peer TCP finite state machine based on RFC 9293.          *)
(* Models connection-state transitions only. Sequence numbers, windows,   *)
(* and retransmission are not modeled.                                    *)
(*                                                                         *)
(*   tcb[p]       : whether peer p has a TCP control block                *)
(*   connstate[p] : the connection state of peer p                        *)
(*   network[p]   : sequence of messages in flight towards peer p         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT peers

ASSUME Cardinality(peers) = 2

VARIABLES tcb, connstate, network

vars == <<tcb, connstate, network>>

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSE-WAIT", "CLOSING",
           "LAST-ACK", "TIME-WAIT"}

Messages == {"SYN", "SYN,ACK", "ACK", "RST", "FIN"}

Other(p) == CHOOSE q \in peers : q # p

-----------------------------------------------------------------------------
(* Helpers for manipulating the network. *)

\* Send message m from p to the other peer.
SendMsg(p, m) ==
    network' = [network EXCEPT ![Other(p)] = Append(@, m)]

\* Peer p consumes the head of its inbox.
RecvMsg(p) ==
    network' = [network EXCEPT ![p] = Tail(@)]

\* Peer p consumes the head of its inbox and sends m to the other peer.
RecvSendMsg(p, m) ==
    network' = [network EXCEPT ![p] = Tail(@),
                               ![Other(p)] = Append(@, m)]

HasHead(p, m) ==
    /\ network[p] # <<>>
    /\ Head(network[p]) = m

-----------------------------------------------------------------------------
TypeOK ==
    /\ tcb \in [peers -> BOOLEAN]
    /\ connstate \in [peers -> States]
    /\ network \in [peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in peers |-> FALSE]
    /\ connstate = [p \in peers |-> "CLOSED"]
    /\ network = [p \in peers |-> <<>>]

-----------------------------------------------------------------------------
(***************************************************************************)
(* User-triggered actions.                                                *)
(***************************************************************************)

\* OPEN call, passive: CLOSED -> LISTEN.
PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "LISTEN"]
    /\ UNCHANGED network

\* OPEN call, active: CLOSED -> SYN-SENT, send SYN.
ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendMsg(p, "SYN")

\* SEND call in LISTEN: LISTEN -> SYN-SENT, send SYN.
SendFromListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendMsg(p, "SYN")
    /\ UNCHANGED tcb

\* CLOSE call in LISTEN: delete TCB, go to CLOSED.
CloseListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

\* CLOSE call in SYN-SENT: delete TCB, go to CLOSED.
\* (This action is given weak fairness to avoid getting stuck in SYN-SENT.)
CloseSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

\* CLOSE call in SYN-RECEIVED or ESTABLISHED: send FIN, go to FIN-WAIT-1.
CloseSynRcvdOrEstablished(p) ==
    /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
    /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-1"]
    /\ SendMsg(p, "FIN")
    /\ UNCHANGED tcb

\* CLOSE call in CLOSE-WAIT: send FIN, go to LAST-ACK.
CloseCloseWait(p) ==
    /\ connstate[p] = "CLOSE-WAIT"
    /\ connstate' = [connstate EXCEPT ![p] = "LAST-ACK"]
    /\ SendMsg(p, "FIN")
    /\ UNCHANGED tcb

\* ABORT call: applicable broadly across synchronized states.
\* Sends RST, deletes TCB, goes to CLOSED.
Abort(p) ==
    /\ connstate[p] \notin {"CLOSED", "LISTEN", "SYN-SENT"}
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ SendMsg(p, "RST")

User(p) ==
    \/ PassiveOpen(p)
    \/ ActiveOpen(p)
    \/ SendFromListen(p)
    \/ CloseListen(p)
    \/ CloseSynSent(p)
    \/ CloseSynRcvdOrEstablished(p)
    \/ CloseCloseWait(p)
    \/ Abort(p)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Protocol-driven (system) transitions.                                  *)
(***************************************************************************)

\* LISTEN: receive SYN, send SYN,ACK, go to SYN-RECEIVED.
ListenRcvSyn(p) ==
    /\ connstate[p] = "LISTEN"
    /\ HasHead(p, "SYN")
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-RECEIVED"]
    /\ RecvSendMsg(p, "SYN,ACK")
    /\ UNCHANGED tcb

\* SYN-SENT: receive SYN,ACK, send ACK, go to ESTABLISHED.
SynSentRcvSynAck(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HasHead(p, "SYN,ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "ESTABLISHED"]
    /\ RecvSendMsg(p, "ACK")
    /\ UNCHANGED tcb

\* SYN-SENT: receive SYN (simultaneous open), send ACK, go to SYN-RECEIVED.
SynSentRcvSyn(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HasHead(p, "SYN")
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-RECEIVED"]
    /\ RecvSendMsg(p, "ACK")
    /\ UNCHANGED tcb

\* SYN-RECEIVED: receive ACK of SYN, go to ESTABLISHED.
SynRcvdRcvAck(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ HasHead(p, "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "ESTABLISHED"]
    /\ RecvMsg(p)
    /\ UNCHANGED tcb

\* ESTABLISHED: receive FIN, send ACK, go to CLOSE-WAIT.
EstablishedRcvFin(p) ==
    /\ connstate[p] = "ESTABLISHED"
    /\ HasHead(p, "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSE-WAIT"]
    /\ RecvSendMsg(p, "ACK")
    /\ UNCHANGED tcb

\* FIN-WAIT-1: receive ACK of FIN, go to FIN-WAIT-2.
FinWait1RcvAck(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasHead(p, "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-2"]
    /\ RecvMsg(p)
    /\ UNCHANGED tcb

\* FIN-WAIT-1: receive FIN, send ACK, go to CLOSING (simultaneous close).
FinWait1RcvFin(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasHead(p, "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSING"]
    /\ RecvSendMsg(p, "ACK")
    /\ UNCHANGED tcb

\* RFC note: FIN-WAIT-1 receiving FIN together with the ACK of its own FIN
\* shortcuts directly to TIME-WAIT, sending an ACK.
FinWait1ToTimeWait(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ Len(network[p]) >= 2
    /\ network[p][1] = "ACK"
    /\ network[p][2] = "FIN"
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ network' = [network EXCEPT ![p] = SubSeq(@, 3, Len(@)),
                                  ![Other(p)] = Append(@, "ACK")]
    /\ UNCHANGED tcb

\* FIN-WAIT-2: receive FIN, send ACK, go to TIME-WAIT.
FinWait2RcvFin(p) ==
    /\ connstate[p] = "FIN-WAIT-2"
    /\ HasHead(p, "FIN")
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ RecvSendMsg(p, "ACK")
    /\ UNCHANGED tcb

\* CLOSING: receive ACK of FIN, go to TIME-WAIT.
ClosingRcvAck(p) ==
    /\ connstate[p] = "CLOSING"
    /\ HasHead(p, "ACK")
    /\ connstate' = [connstate EXCEPT ![p] = "TIME-WAIT"]
    /\ RecvMsg(p)
    /\ UNCHANGED tcb

\* LAST-ACK: receive ACK of FIN, delete TCB, go to CLOSED.
LastAckRcvAck(p) ==
    /\ connstate[p] = "LAST-ACK"
    /\ HasHead(p, "ACK")
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ RecvMsg(p)

\* TIME-WAIT: timeout (2 MSL), delete TCB, go to CLOSED.
TimeWaitTimeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

\* Receiving RST in any state other than CLOSED and LISTEN:
\* delete TCB and go to CLOSED.
RcvRst(p) ==
    /\ connstate[p] \notin {"CLOSED", "LISTEN"}
    /\ HasHead(p, "RST")
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ RecvMsg(p)

\* LISTEN: an incoming RST is ignored; an incoming ACK or SYN,ACK
\* is answered with RST.
ListenRcvOther(p) ==
    /\ connstate[p] = "LISTEN"
    /\ network[p] # <<>>
    /\ Head(network[p]) \in {"RST", "ACK", "SYN,ACK", "FIN"}
    /\ IF Head(network[p]) \in {"ACK", "SYN,ACK"}
          THEN RecvSendMsg(p, "RST")
          ELSE RecvMsg(p)
    /\ UNCHANGED <<tcb, connstate>>

\* CLOSED: any incoming segment is discarded; a non-RST segment
\* is answered with RST.
ClosedRcv(p) ==
    /\ connstate[p] = "CLOSED"
    /\ network[p] # <<>>
    /\ IF Head(network[p]) = "RST"
          THEN RecvMsg(p)
          ELSE RecvSendMsg(p, "RST")
    /\ UNCHANGED <<tcb, connstate>>

System(p) ==
    \/ ListenRcvSyn(p)
    \/ SynSentRcvSynAck(p)
    \/ SynSentRcvSyn(p)
    \/ SynRcvdRcvAck(p)
    \/ EstablishedRcvFin(p)
    \/ FinWait1RcvAck(p)
    \/ FinWait1RcvFin(p)
    \/ FinWait1ToTimeWait(p)
    \/ FinWait2RcvFin(p)
    \/ ClosingRcvAck(p)
    \/ LastAckRcvAck(p)
    \/ TimeWaitTimeout(p)
    \/ RcvRst(p)
    \/ ListenRcvOther(p)
    \/ ClosedRcv(p)

-----------------------------------------------------------------------------
Next ==
    \E p \in peers : User(p) \/ System(p)

Fairness ==
    /\ \A p \in peers : WF_vars(System(p))
    /\ \A p \in peers : WF_vars(CloseSynSent(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                             *)
(***************************************************************************)

\* When no messages are in flight, either both peers are ESTABLISHED
\* or neither is.
Inv ==
    (\A p \in peers : network[p] = <<>>)
        => (\A p, q \in peers :
               connstate[p] = "ESTABLISHED" <=> connstate[q] = "ESTABLISHED")

\* A peer in SYN-SENT eventually reaches ESTABLISHED, LISTEN, or CLOSED.
SynSentLeadsTo ==
    \A p \in peers :
        connstate[p] = "SYN-SENT"
            ~> connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => SynSentLeadsTo
=============================================================================
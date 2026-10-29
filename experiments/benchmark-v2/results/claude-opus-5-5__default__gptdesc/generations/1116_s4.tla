--------------------------------- MODULE tcp ---------------------------------
(***************************************************************************)
(* An abstract model of the TCP finite state machine for two peers, based *)
(* on RFC 9293. It models connection-state transitions only. Sequence     *)
(* numbers, windows and data transfer are not modeled.                    *)
(*                                                                         *)
(*  - tcb[p]       : whether peer p has a TCP control block               *)
(*  - connstate[p] : the connection state of peer p                       *)
(*  - network[p]   : the sequence of messages in flight to peer p         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Peers

ASSUME Cardinality(Peers) = 2

VARIABLES tcb, connstate, network

vars == <<tcb, connstate, network>>

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "CLOSE-WAIT",
           "LAST-ACK", "TIME-WAIT"}

Messages == {"SYN", "SYN,ACK", "ACK", "FIN", "FIN,ACK", "RST"}

\* The other peer.
Peer(p) == CHOOSE q \in Peers : q # p

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

-----------------------------------------------------------------------------
(* Helper operators *)

\* Send message m to the peer of p.
SendTo(p, m) ==
    network' = [network EXCEPT ![Peer(p)] = Append(@, m)]

\* p consumes the head of its inbox.
Consume(p) ==
    network' = [network EXCEPT ![p] = Tail(@)]

\* p consumes the head of its inbox and replies with message m.
ConsumeAndReply(p, m) ==
    network' = [network EXCEPT ![p] = Tail(@),
                               ![Peer(p)] = Append(@, m)]

Head_(p) == Head(network[p])

HasMsg(p, m) == network[p] # <<>> /\ Head(network[p]) = m

SetState(p, s) == connstate' = [connstate EXCEPT ![p] = s]

-----------------------------------------------------------------------------
(* User-triggered actions *)

\* Passive OPEN: create TCB and go to LISTEN.
PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ SetState(p, "LISTEN")
    /\ UNCHANGED network

\* Active OPEN: create TCB, send SYN, go to SYN-SENT.
ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ SetState(p, "SYN-SENT")
    /\ SendTo(p, "SYN")

\* SEND in LISTEN: send SYN, go to SYN-SENT.
SendInListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ SetState(p, "SYN-SENT")
    /\ SendTo(p, "SYN")
    /\ UNCHANGED tcb

\* CLOSE in LISTEN: delete TCB.
CloseListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ UNCHANGED network

\* CLOSE in SYN-SENT: delete TCB.
CloseSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ UNCHANGED network

\* CLOSE in SYN-RECEIVED or ESTABLISHED: send FIN, go to FIN-WAIT-1.
CloseToFinWait1(p) ==
    /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
    /\ SetState(p, "FIN-WAIT-1")
    /\ SendTo(p, "FIN")
    /\ UNCHANGED tcb

\* CLOSE in CLOSE-WAIT: send FIN, go to LAST-ACK.
CloseCloseWait(p) ==
    /\ connstate[p] = "CLOSE-WAIT"
    /\ SetState(p, "LAST-ACK")
    /\ SendTo(p, "FIN")
    /\ UNCHANGED tcb

\* ABORT / reset: applicable in any state with a TCB. Delete TCB, send RST.
Abort(p) ==
    /\ connstate[p] \notin {"CLOSED"}
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ SendTo(p, "RST")

User(p) ==
    \/ PassiveOpen(p)
    \/ ActiveOpen(p)
    \/ SendInListen(p)
    \/ CloseListen(p)
    \/ CloseSynSent(p)
    \/ CloseToFinWait1(p)
    \/ CloseCloseWait(p)
    \/ Abort(p)

-----------------------------------------------------------------------------
(* Protocol-driven (system) actions *)

\* CLOSED: any non-RST segment is answered by RST; RST is dropped.
RcvInClosed(p) ==
    /\ connstate[p] = "CLOSED"
    /\ network[p] # <<>>
    /\ IF Head_(p) = "RST"
         THEN Consume(p)
         ELSE ConsumeAndReply(p, "RST")
    /\ UNCHANGED <<tcb, connstate>>

\* LISTEN receives SYN: reply SYN,ACK, go to SYN-RECEIVED.
ListenRcvSyn(p) ==
    /\ connstate[p] = "LISTEN"
    /\ HasMsg(p, "SYN")
    /\ SetState(p, "SYN-RECEIVED")
    /\ ConsumeAndReply(p, "SYN,ACK")
    /\ UNCHANGED tcb

\* SYN-SENT receives SYN,ACK: reply ACK, go to ESTABLISHED.
SynSentRcvSynAck(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HasMsg(p, "SYN,ACK")
    /\ SetState(p, "ESTABLISHED")
    /\ ConsumeAndReply(p, "ACK")
    /\ UNCHANGED tcb

\* SYN-SENT receives SYN (simultaneous open): reply SYN,ACK, go to SYN-RECEIVED.
SynSentRcvSyn(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HasMsg(p, "SYN")
    /\ SetState(p, "SYN-RECEIVED")
    /\ ConsumeAndReply(p, "SYN,ACK")
    /\ UNCHANGED tcb

\* SYN-RECEIVED receives ACK (or SYN,ACK in simultaneous open): ESTABLISHED.
SynRcvdRcvAck(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ network[p] # <<>>
    /\ Head_(p) \in {"ACK", "SYN,ACK"}
    /\ SetState(p, "ESTABLISHED")
    /\ Consume(p)
    /\ UNCHANGED tcb

\* ESTABLISHED receives FIN: reply ACK, go to CLOSE-WAIT.
EstablishedRcvFin(p) ==
    /\ connstate[p] = "ESTABLISHED"
    /\ HasMsg(p, "FIN")
    /\ SetState(p, "CLOSE-WAIT")
    /\ ConsumeAndReply(p, "ACK")
    /\ UNCHANGED tcb

\* FIN-WAIT-1 receives ACK of FIN: go to FIN-WAIT-2.
FinWait1RcvAck(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasMsg(p, "ACK")
    /\ SetState(p, "FIN-WAIT-2")
    /\ Consume(p)
    /\ UNCHANGED tcb

\* FIN-WAIT-1 receives FIN: reply ACK, go to CLOSING.
FinWait1RcvFin(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasMsg(p, "FIN")
    /\ SetState(p, "CLOSING")
    /\ ConsumeAndReply(p, "ACK")
    /\ UNCHANGED tcb

\* RFC note: FIN-WAIT-1 receives FIN,ACK: reply ACK, go directly to TIME-WAIT.
FinWait1RcvFinAck(p) ==
    /\ connstate[p] = "FIN-WAIT-1"
    /\ HasMsg(p, "FIN,ACK")
    /\ SetState(p, "TIME-WAIT")
    /\ ConsumeAndReply(p, "ACK")
    /\ UNCHANGED tcb

\* FIN-WAIT-2 receives FIN: reply ACK, go to TIME-WAIT.
FinWait2RcvFin(p) ==
    /\ connstate[p] = "FIN-WAIT-2"
    /\ network[p] # <<>>
    /\ Head_(p) \in {"FIN", "FIN,ACK"}
    /\ SetState(p, "TIME-WAIT")
    /\ ConsumeAndReply(p, "ACK")
    /\ UNCHANGED tcb

\* CLOSING receives ACK of FIN: go to TIME-WAIT.
ClosingRcvAck(p) ==
    /\ connstate[p] = "CLOSING"
    /\ HasMsg(p, "ACK")
    /\ SetState(p, "TIME-WAIT")
    /\ Consume(p)
    /\ UNCHANGED tcb

\* LAST-ACK receives ACK of FIN: delete TCB, go to CLOSED.
LastAckRcvAck(p) ==
    /\ connstate[p] = "LAST-ACK"
    /\ HasMsg(p, "ACK")
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ Consume(p)

\* TIME-WAIT timeout (2 MSL): delete TCB, go to CLOSED.
TimeWaitTimeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ UNCHANGED network

\* Reception of RST in any synchronized or handshake state: delete TCB, CLOSED.
RcvRst(p) ==
    /\ connstate[p] \notin {"CLOSED", "LISTEN"}
    /\ HasMsg(p, "RST")
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ Consume(p)

\* Segments that are not handled by any transition above are discarded.
Handled(p) ==
    \/ connstate[p] = "CLOSED"
    \/ connstate[p] = "LISTEN"       /\ Head_(p) = "SYN"
    \/ connstate[p] = "SYN-SENT"     /\ Head_(p) \in {"SYN", "SYN,ACK"}
    \/ connstate[p] = "SYN-RECEIVED" /\ Head_(p) \in {"ACK", "SYN,ACK"}
    \/ connstate[p] = "ESTABLISHED"  /\ Head_(p) = "FIN"
    \/ connstate[p] = "FIN-WAIT-1"   /\ Head_(p) \in {"ACK", "FIN", "FIN,ACK"}
    \/ connstate[p] = "FIN-WAIT-2"   /\ Head_(p) \in {"FIN", "FIN,ACK"}
    \/ connstate[p] = "CLOSING"      /\ Head_(p) = "ACK"
    \/ connstate[p] = "LAST-ACK"     /\ Head_(p) = "ACK"
    \/ connstate[p] \notin {"CLOSED", "LISTEN"} /\ Head_(p) = "RST"

Discard(p) ==
    /\ network[p] # <<>>
    /\ ~Handled(p)
    /\ Consume(p)
    /\ UNCHANGED <<tcb, connstate>>

System(p) ==
    \/ RcvInClosed(p)
    \/ ListenRcvSyn(p)
    \/ SynSentRcvSynAck(p)
    \/ SynSentRcvSyn(p)
    \/ SynRcvdRcvAck(p)
    \/ EstablishedRcvFin(p)
    \/ FinWait1RcvAck(p)
    \/ FinWait1RcvFin(p)
    \/ FinWait1RcvFinAck(p)
    \/ FinWait2RcvFin(p)
    \/ ClosingRcvAck(p)
    \/ LastAckRcvAck(p)
    \/ TimeWaitTimeout(p)
    \/ RcvRst(p)
    \/ Discard(p)

-----------------------------------------------------------------------------

Next == \E p \in Peers : User(p) \/ System(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Peers : System(p))
    /\ WF_vars(\E p \in Peers : CloseSynSent(p))

-----------------------------------------------------------------------------
(* Properties *)

\* When no messages are in flight, the peers agree on being ESTABLISHED.
Inv ==
    (\A p \in Peers : network[p] = <<>>) =>
        \A p, q \in Peers :
            (connstate[p] = "ESTABLISHED") <=> (connstate[q] = "ESTABLISHED")

\* A peer in SYN-SENT eventually reaches ESTABLISHED, LISTEN or CLOSED.
Prop ==
    \A p \in Peers :
        connstate[p] = "SYN-SENT" ~>
            connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Prop

=============================================================================
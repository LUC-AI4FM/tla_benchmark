------------------------------ MODULE TCPHandshake ------------------------------
(***************************************************************************)
(* TCP connection establishment (three-way handshake) between two peers.  *)
(* Each peer keeps a connection state and a TCB flag. Peers talk over      *)
(* per-peer FIFO incoming queues. The network is unreliable: it may lose   *)
(* a bounded number of messages (MaxLoss). Lost messages are recovered by  *)
(* timeout-driven retransmission.                                          *)
(* The model covers both active open and passive open, including           *)
(* simultaneous open.                                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Peers,      \* the two communicating peers
          MaxLoss     \* bound on the number of messages the network may lose

ASSUME Cardinality(Peers) = 2
ASSUME MaxLoss \in Nat

VARIABLES connstate,  \* connstate[p] : TCP state of peer p
          tcb,        \* tcb[p]       : TRUE iff a TCB (connection context) exists at p
          network,    \* network[p]   : queue of messages destined to peer p
          losses      \* number of messages lost so far

vars == <<connstate, tcb, network, losses>>

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED"}
Msgs   == {"SYN", "SYN,ACK", "ACK"}

Other(p) == CHOOSE q \in Peers : q # p

\* Append m to queue s, unless it would duplicate the last queued message
Push(s, m) == IF s # <<>> /\ s[Len(s)] = m THEN s ELSE Append(s, m)

HeadIs(p, m) == network[p] # <<>> /\ Head(network[p]) = m

\* Consume the head of p's queue and send m to the other peer
ConsumeAndReply(p, m) ==
    network' = [network EXCEPT ![p] = Tail(@), ![Other(p)] = Push(@, m)]

\* Consume the head of p's queue without replying
Consume(p) == network' = [network EXCEPT ![p] = Tail(@)]

\* Send m to the other peer without consuming anything
SendTo(p, m) == network' = [network EXCEPT ![Other(p)] = Push(@, m)]

SetState(p, s) == connstate' = [connstate EXCEPT ![p] = s]

-----------------------------------------------------------------------------
TypeOK ==
    /\ connstate \in [Peers -> States]
    /\ tcb \in [Peers -> BOOLEAN]
    /\ network \in [Peers -> Seq(Msgs)]
    /\ losses \in 0..MaxLoss

Init ==
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ tcb = [p \in Peers |-> FALSE]
    /\ network = [p \in Peers |-> <<>>]
    /\ losses = 0

-----------------------------------------------------------------------------
(* User calls *)

\* Passive open: CLOSED -> LISTEN (create TCB)
PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ SetState(p, "LISTEN")
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<network, losses>>

\* Active open: CLOSED -> SYN-SENT (create TCB, send SYN)
ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ SetState(p, "SYN-SENT")
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ SendTo(p, "SYN")
    /\ UNCHANGED losses

\* SEND call in LISTEN: LISTEN -> SYN-SENT (send SYN)
ListenSend(p) ==
    /\ connstate[p] = "LISTEN"
    /\ SetState(p, "SYN-SENT")
    /\ SendTo(p, "SYN")
    /\ UNCHANGED <<tcb, losses>>

-----------------------------------------------------------------------------
(* Segment arrivals *)

\* LISTEN receives SYN: -> SYN-RECEIVED, reply SYN,ACK
RcvSynListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ HeadIs(p, "SYN")
    /\ SetState(p, "SYN-RECEIVED")
    /\ ConsumeAndReply(p, "SYN,ACK")
    /\ UNCHANGED <<tcb, losses>>

\* SYN-SENT receives SYN (simultaneous open): -> SYN-RECEIVED, reply SYN,ACK
RcvSynSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HeadIs(p, "SYN")
    /\ SetState(p, "SYN-RECEIVED")
    /\ ConsumeAndReply(p, "SYN,ACK")
    /\ UNCHANGED <<tcb, losses>>

\* SYN-SENT receives SYN,ACK: -> ESTABLISHED, reply ACK
RcvSynAckSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ HeadIs(p, "SYN,ACK")
    /\ SetState(p, "ESTABLISHED")
    /\ ConsumeAndReply(p, "ACK")
    /\ UNCHANGED <<tcb, losses>>

\* SYN-RECEIVED receives ACK: -> ESTABLISHED
RcvAckSynRcvd(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ HeadIs(p, "ACK")
    /\ SetState(p, "ESTABLISHED")
    /\ Consume(p)
    /\ UNCHANGED <<tcb, losses>>

\* SYN-RECEIVED receives SYN,ACK (simultaneous open): -> ESTABLISHED
RcvSynAckSynRcvd(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ HeadIs(p, "SYN,ACK")
    /\ SetState(p, "ESTABLISHED")
    /\ Consume(p)
    /\ UNCHANGED <<tcb, losses>>

\* SYN-RECEIVED receives a retransmitted SYN: re-send SYN,ACK
RcvSynSynRcvd(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ HeadIs(p, "SYN")
    /\ ConsumeAndReply(p, "SYN,ACK")
    /\ UNCHANGED <<connstate, tcb, losses>>

\* ESTABLISHED receives a retransmitted SYN,ACK: re-send ACK
RcvSynAckEst(p) ==
    /\ connstate[p] = "ESTABLISHED"
    /\ HeadIs(p, "SYN,ACK")
    /\ ConsumeAndReply(p, "ACK")
    /\ UNCHANGED <<connstate, tcb, losses>>

\* Segments that are not acceptable in the current state are dropped
Unexpected(s) ==
    CASE s = "LISTEN"       -> {"SYN,ACK", "ACK"}
      [] s = "SYN-SENT"     -> {"ACK"}
      [] s = "ESTABLISHED"  -> {"SYN", "ACK"}
      [] OTHER              -> {}

Discard(p) ==
    /\ network[p] # <<>>
    /\ Head(network[p]) \in Unexpected(connstate[p])
    /\ Consume(p)
    /\ UNCHANGED <<connstate, tcb, losses>>

-----------------------------------------------------------------------------
(* Timeouts and network faults *)

\* Retransmission timeout: no traffic in flight, so re-send the pending
\* control segment
Retransmit(p) ==
    /\ connstate[p] \in {"SYN-SENT", "SYN-RECEIVED"}
    /\ network[p] = <<>>
    /\ network[Other(p)] = <<>>
    /\ SendTo(p, IF connstate[p] = "SYN-SENT" THEN "SYN" ELSE "SYN,ACK")
    /\ UNCHANGED <<connstate, tcb, losses>>

\* The network loses the message at the head of p's queue
Lose(p) ==
    /\ losses < MaxLoss
    /\ network[p] # <<>>
    /\ network' = [network EXCEPT ![p] = Tail(@)]
    /\ losses' = losses + 1
    /\ UNCHANGED <<connstate, tcb>>

\* Both peers established and network drained: stutter to avoid deadlock
Done ==
    /\ \A p \in Peers : connstate[p] = "ESTABLISHED" /\ network[p] = <<>>
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
PeerNext(p) ==
    \/ PassiveOpen(p)
    \/ ActiveOpen(p)
    \/ ListenSend(p)
    \/ RcvSynListen(p)
    \/ RcvSynSynSent(p)
    \/ RcvSynAckSynSent(p)
    \/ RcvAckSynRcvd(p)
    \/ RcvSynAckSynRcvd(p)
    \/ RcvSynSynRcvd(p)
    \/ RcvSynAckEst(p)
    \/ Discard(p)
    \/ Retransmit(p)

Next ==
    \/ \E p \in Peers : PeerNext(p)
    \/ \E p \in Peers : Lose(p)
    \/ Done

Fairness ==
    \A p \in Peers :
        /\ WF_vars(PassiveOpen(p))
        /\ WF_vars(ActiveOpen(p))
        /\ WF_vars(ListenSend(p))
        /\ WF_vars(RcvSynListen(p))
        /\ WF_vars(RcvSynSynSent(p))
        /\ WF_vars(RcvSynAckSynSent(p))
        /\ WF_vars(RcvAckSynRcvd(p))
        /\ WF_vars(RcvSynAckSynRcvd(p))
        /\ WF_vars(RcvSynSynRcvd(p))
        /\ WF_vars(RcvSynAckEst(p))
        /\ WF_vars(Discard(p))
        /\ WF_vars(Retransmit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* A TCB exists exactly when the peer is not CLOSED
TCBConsistency ==
    \A p \in Peers : tcb[p] = (connstate[p] # "CLOSED")

\* Mutual consistency of the two peers' states per the TCP state machine
StateConsistency ==
    /\ TCBConsistency
    /\ \A p \in Peers :
         /\ connstate[p] = "ESTABLISHED" =>
              connstate[Other(p)] \in {"SYN-RECEIVED", "ESTABLISHED"}
         /\ connstate[p] = "SYN-RECEIVED" =>
              connstate[Other(p)] \in {"SYN-SENT", "SYN-RECEIVED", "ESTABLISHED"}

\* Consecutive messages in any incoming queue are never duplicates
NoSpuriousRetransmission ==
    \A p \in Peers :
        \A i \in 1..Len(network[p]) :
            i < Len(network[p]) => network[p][i] # network[p][i + 1]

(* Liveness properties *)

\* Both peers eventually reach ESTABLISHED
ConnectionEstablished ==
    <>(\A p \in Peers : connstate[p] = "ESTABLISHED")

\* Once established, a peer stays established
EstablishedStable ==
    \A p \in Peers : [](connstate[p] = "ESTABLISHED" => [](connstate[p] = "ESTABLISHED"))

(* Symmetry set for model checking with a fixed pair of peers *)
Symmetry == Permutations(Peers)

THEOREM Spec => [](TypeOK /\ StateConsistency /\ NoSpuriousRetransmission)
THEOREM Spec => ConnectionEstablished /\ EstablishedStable
=============================================================================
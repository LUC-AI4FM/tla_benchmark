---------------------------- MODULE TCP ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Peers

ASSUME Cardinality(Peers) = 2

VARIABLES tcb, connstate, network

vars == <<tcb, connstate, network>>

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "CLOSE-WAIT", "LAST-ACK",
           "TIME-WAIT"}

Messages == {"SYN", "SYN,ACK", "ACK", "RST", "FIN", "ACKofFIN"}

MaxInFlight == 3

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

InFlight == Len(network[CHOOSE p \in Peers : TRUE])
            + Len(network[CHOOSE p \in Peers : p # CHOOSE q \in Peers : TRUE])

CanSend == InFlight < MaxInFlight

Send(remote, msg) == network' = [network EXCEPT ![remote] = Append(@, msg)]

HasMsg(local, msg) == network[local] # <<>> /\ Head(network[local]) = msg

Consume(local) == network' = [network EXCEPT ![local] = Tail(@)]

ConsumeAndSend(local, remote, msg) ==
    network' = [network EXCEPT ![local] = Tail(@), ![remote] = Append(@, msg)]

GoTo(local, s) == connstate' = [connstate EXCEPT ![local] = s]

-----------------------------------------------------------------------------
(* User commands *)

PASSIVE_OPEN(local, remote) ==
    /\ connstate[local] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![local] = TRUE]
    /\ GoTo(local, "LISTEN")
    /\ UNCHANGED network

ACTIVE_OPEN(local, remote) ==
    /\ connstate[local] = "CLOSED"
    /\ CanSend
    /\ tcb' = [tcb EXCEPT ![local] = TRUE]
    /\ GoTo(local, "SYN-SENT")
    /\ Send(remote, "SYN")

SEND(local, remote) ==
    /\ connstate[local] = "LISTEN"
    /\ CanSend
    /\ GoTo(local, "SYN-SENT")
    /\ Send(remote, "SYN")
    /\ UNCHANGED tcb

CLOSE_LISTEN(local, remote) ==
    /\ connstate[local] = "LISTEN"
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    /\ GoTo(local, "CLOSED")
    /\ UNCHANGED network

CLOSE_SYN_SENT(local, remote) ==
    /\ connstate[local] = "SYN-SENT"
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    /\ GoTo(local, "CLOSED")
    /\ UNCHANGED network

CLOSE_SYN_RECEIVED(local, remote) ==
    /\ connstate[local] = "SYN-RECEIVED"
    /\ GoTo(local, "FIN-WAIT-1")
    /\ Send(remote, "FIN")
    /\ UNCHANGED tcb

CLOSE_ESTABLISHED(local, remote) ==
    /\ connstate[local] = "ESTABLISHED"
    /\ GoTo(local, "FIN-WAIT-1")
    /\ Send(remote, "FIN")
    /\ UNCHANGED tcb

CLOSE_CLOSE_WAIT(local, remote) ==
    /\ connstate[local] = "CLOSE-WAIT"
    /\ GoTo(local, "LAST-ACK")
    /\ Send(remote, "FIN")
    /\ UNCHANGED tcb

UserAction(local, remote) ==
    \/ PASSIVE_OPEN(local, remote)
    \/ ACTIVE_OPEN(local, remote)
    \/ SEND(local, remote)
    \/ CLOSE_LISTEN(local, remote)
    \/ CLOSE_SYN_SENT(local, remote)
    \/ CLOSE_SYN_RECEIVED(local, remote)
    \/ CLOSE_ESTABLISHED(local, remote)
    \/ CLOSE_CLOSE_WAIT(local, remote)

-----------------------------------------------------------------------------
(* System actions: segment processing *)

ListenSyn(local, remote) ==
    /\ connstate[local] = "LISTEN"
    /\ HasMsg(local, "SYN")
    /\ GoTo(local, "SYN-RECEIVED")
    /\ ConsumeAndSend(local, remote, "SYN,ACK")
    /\ UNCHANGED tcb

SynSentSynAck(local, remote) ==
    /\ connstate[local] = "SYN-SENT"
    /\ HasMsg(local, "SYN,ACK")
    /\ GoTo(local, "ESTABLISHED")
    /\ ConsumeAndSend(local, remote, "ACK")
    /\ UNCHANGED tcb

SynSentSyn(local, remote) ==
    /\ connstate[local] = "SYN-SENT"
    /\ HasMsg(local, "SYN")
    /\ GoTo(local, "SYN-RECEIVED")
    /\ ConsumeAndSend(local, remote, "SYN,ACK")
    /\ UNCHANGED tcb

SynReceivedAck(local, remote) ==
    /\ connstate[local] = "SYN-RECEIVED"
    /\ (HasMsg(local, "ACK") \/ HasMsg(local, "SYN,ACK"))
    /\ GoTo(local, "ESTABLISHED")
    /\ Consume(local)
    /\ UNCHANGED tcb

EstablishedFin(local, remote) ==
    /\ connstate[local] = "ESTABLISHED"
    /\ HasMsg(local, "FIN")
    /\ GoTo(local, "CLOSE-WAIT")
    /\ ConsumeAndSend(local, remote, "ACKofFIN")
    /\ UNCHANGED tcb

FinWait1AckOfFin(local, remote) ==
    /\ connstate[local] = "FIN-WAIT-1"
    /\ HasMsg(local, "ACKofFIN")
    /\ GoTo(local, "FIN-WAIT-2")
    /\ Consume(local)
    /\ UNCHANGED tcb

FinWait1Fin(local, remote) ==
    /\ connstate[local] = "FIN-WAIT-1"
    /\ HasMsg(local, "FIN")
    /\ GoTo(local, "CLOSING")
    /\ ConsumeAndSend(local, remote, "ACKofFIN")
    /\ UNCHANGED tcb

FinWait2Fin(local, remote) ==
    /\ connstate[local] = "FIN-WAIT-2"
    /\ HasMsg(local, "FIN")
    /\ GoTo(local, "TIME-WAIT")
    /\ ConsumeAndSend(local, remote, "ACKofFIN")
    /\ UNCHANGED tcb

ClosingAckOfFin(local, remote) ==
    /\ connstate[local] = "CLOSING"
    /\ HasMsg(local, "ACKofFIN")
    /\ GoTo(local, "TIME-WAIT")
    /\ Consume(local)
    /\ UNCHANGED tcb

LastAckAckOfFin(local, remote) ==
    /\ connstate[local] = "LAST-ACK"
    /\ HasMsg(local, "ACKofFIN")
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    /\ GoTo(local, "CLOSED")
    /\ Consume(local)

TimeWaitTimeout(local, remote) ==
    /\ connstate[local] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![local] = FALSE]
    /\ GoTo(local, "CLOSED")
    /\ UNCHANGED network

ClosedSegment(local, remote) ==
    /\ connstate[local] = "CLOSED"
    /\ network[local] # <<>>
    /\ IF Head(network[local]) = "RST"
          THEN Consume(local)
          ELSE ConsumeAndSend(local, remote, "RST")
    /\ UNCHANGED <<tcb, connstate>>

(* RFC 9293 note 3: reset processing *)
RESET(local, remote) ==
    /\ connstate[local] # "CLOSED"
    /\ HasMsg(local, "RST")
    /\ Consume(local)
    /\ CASE connstate[local] = "LISTEN" ->
                UNCHANGED <<tcb, connstate>>
         [] connstate[local] = "SYN-RECEIVED" ->
                /\ GoTo(local, "LISTEN")
                /\ UNCHANGED tcb
         [] OTHER ->
                /\ GoTo(local, "CLOSED")
                /\ tcb' = [tcb EXCEPT ![local] = FALSE]

SystemAction(local, remote) ==
    \/ ListenSyn(local, remote)
    \/ SynSentSynAck(local, remote)
    \/ SynSentSyn(local, remote)
    \/ SynReceivedAck(local, remote)
    \/ EstablishedFin(local, remote)
    \/ FinWait1AckOfFin(local, remote)
    \/ FinWait1Fin(local, remote)
    \/ FinWait2Fin(local, remote)
    \/ ClosingAckOfFin(local, remote)
    \/ LastAckAckOfFin(local, remote)
    \/ TimeWaitTimeout(local, remote)
    \/ ClosedSegment(local, remote)

-----------------------------------------------------------------------------

Next ==
    \E local, remote \in Peers :
        /\ local # remote
        /\ \/ UserAction(local, remote)
           \/ SystemAction(local, remote)
           \/ RESET(local, remote)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E local, remote \in Peers :
                  local # remote /\ SystemAction(local, remote))
    /\ WF_vars(\E local, remote \in Peers :
                  local # remote /\ CLOSE_SYN_SENT(local, remote))

-----------------------------------------------------------------------------

Inv ==
    \A p, q \in Peers :
        (/\ p # q
         /\ network[p] = <<>>
         /\ network[q] = <<>>
         /\ connstate[p] = "ESTABLISHED")
        => connstate[q] = "ESTABLISHED"

Prop ==
    \A p \in Peers :
        connstate[p] = "SYN-SENT" ~>
            connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}

=============================================================================
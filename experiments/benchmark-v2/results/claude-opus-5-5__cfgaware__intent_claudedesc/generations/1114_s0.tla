---------------------------- MODULE tcp ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS A, B

CONSTANT Peers

peers == {A, B}

VARIABLES
    tcb,        \* tcb[p] : TRUE iff a transmission control block exists at p
    connstate,  \* connstate[p] : current TCP connection state of peer p
    network     \* network[p] : FIFO queue of messages destined to peer p

vars == <<tcb, connstate, network>>

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED"}

Messages == {"SYN", "SYN,ACK", "ACK"}

Other(p) == CHOOSE q \in Peers : q # p

-----------------------------------------------------------------------------
TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

-----------------------------------------------------------------------------
\* Send message m to peer q
SendTo(q, m) == network' = [network EXCEPT ![q] = Append(@, m)]

\* Passive open: CLOSED -> LISTEN
PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "LISTEN"]
    /\ UNCHANGED network

\* Active open: CLOSED -> SYN-SENT, sending SYN
ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendTo(Other(p), "SYN")

\* SEND call in LISTEN: LISTEN -> SYN-SENT, sending SYN
ListenSend(p) ==
    /\ connstate[p] = "LISTEN"
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendTo(Other(p), "SYN")
    /\ UNCHANGED tcb

\* Processing the message at the head of p's incoming queue
Consume(p, newstate) ==
    connstate' = [connstate EXCEPT ![p] = newstate]

RcvSynInListen(p) ==
    /\ connstate[p] = "LISTEN"
    /\ network[p] # <<>>
    /\ Head(network[p]) = "SYN"
    /\ Consume(p, "SYN-RECEIVED")
    /\ network' = [network EXCEPT ![p] = Tail(@),
                                  ![Other(p)] = Append(@, "SYN,ACK")]
    /\ UNCHANGED tcb

\* Simultaneous open
RcvSynInSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ network[p] # <<>>
    /\ Head(network[p]) = "SYN"
    /\ Consume(p, "SYN-RECEIVED")
    /\ network' = [network EXCEPT ![p] = Tail(@),
                                  ![Other(p)] = Append(@, "SYN,ACK")]
    /\ UNCHANGED tcb

RcvSynAckInSynSent(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ network[p] # <<>>
    /\ Head(network[p]) = "SYN,ACK"
    /\ Consume(p, "ESTABLISHED")
    /\ network' = [network EXCEPT ![p] = Tail(@),
                                  ![Other(p)] = Append(@, "ACK")]
    /\ UNCHANGED tcb

RcvSynAckInSynRcvd(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ network[p] # <<>>
    /\ Head(network[p]) = "SYN,ACK"
    /\ Consume(p, "ESTABLISHED")
    /\ network' = [network EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED tcb

RcvAckInSynRcvd(p) ==
    /\ connstate[p] = "SYN-RECEIVED"
    /\ network[p] # <<>>
    /\ Head(network[p]) = "ACK"
    /\ Consume(p, "ESTABLISHED")
    /\ network' = [network EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED tcb

Receive(p) ==
    \/ RcvSynInListen(p)
    \/ RcvSynInSynSent(p)
    \/ RcvSynAckInSynSent(p)
    \/ RcvSynAckInSynRcvd(p)
    \/ RcvAckInSynRcvd(p)

Next ==
    \E p \in Peers :
        \/ PassiveOpen(p)
        \/ ActiveOpen(p)
        \/ ListenSend(p)
        \/ Receive(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Peers : WF_vars(Receive(p))

-----------------------------------------------------------------------------
\* State consistency between the two peers
Inv ==
    /\ \A p \in Peers : tcb[p] <=> connstate[p] # "CLOSED"
    /\ \A p \in Peers :
        connstate[p] = "ESTABLISHED" =>
            connstate[Other(p)] \in {"SYN-RECEIVED", "ESTABLISHED"}

\* Connection establishment: once one side is established, so is the other
Prop ==
    \A p \in Peers :
        (connstate[p] = "ESTABLISHED") ~> (\A q \in Peers : connstate[q] = "ESTABLISHED")

-----------------------------------------------------------------------------
\* Model-checking helpers

MCInit ==
    /\ Init
    /\ Peers = peers

Symmetry == Permutations(peers)

NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

SingleActiveOpen ==
    ~(\A p \in Peers : connstate[p] = "SYN-SENT")

=============================================================================
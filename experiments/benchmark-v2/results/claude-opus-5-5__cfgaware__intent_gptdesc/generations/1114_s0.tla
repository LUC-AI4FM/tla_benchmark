---------------------------- MODULE TCPHandshake ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS A, B

ASSUME A # B

peers == {A, B}

\* Symmetry set: the spec is invariant under swapping the identities of peers
Peers == Permutations(peers)

VARIABLES state,       \* per-endpoint TCP connection state
          role,        \* "active" or "passive" open
          net,         \* net[<<p,q>>] : FIFO channel of messages from p to q
          rcvd,        \* set of message kinds each endpoint has received
          activeOpens  \* number of active open events performed

vars == <<state, role, net, rcvd, activeOpens>>

States == {"CLOSED", "LISTEN", "SYN_SENT", "SYN_RCVD", "ESTABLISHED"}
Msgs   == {"SYN", "SYNACK", "ACK"}
Roles  == {"active", "passive"}
Chans  == {c \in peers \X peers : c[1] # c[2]}

Other(p) == CHOOSE q \in peers : q # p

\* Sending never places an identical copy immediately after the same message
SendTo(ch, m) == IF ch # <<>> /\ ch[Len(ch)] = m THEN ch ELSE Append(ch, m)

CanSend(ch, m) == ch = <<>> \/ ch[Len(ch)] # m

-----------------------------------------------------------------------------
\* One endpoint performs an active open (sends SYN), the other a passive open.
Init ==
    \E a \in peers :
        LET b == Other(a) IN
        /\ state = [p \in peers |-> IF p = a THEN "SYN_SENT" ELSE "LISTEN"]
        /\ role  = [p \in peers |-> IF p = a THEN "active" ELSE "passive"]
        /\ net   = [c \in Chans |-> IF c = <<a, b>> THEN <<"SYN">> ELSE <<>>]
        /\ rcvd  = [p \in peers |-> {}]
        /\ activeOpens = 1

MCInit == Init

-----------------------------------------------------------------------------
\* Endpoint p receives (and processes) the head message on the channel from q
Receive(p) ==
    \E q \in peers \ {p} :
        LET in  == <<q, p>>
            out == <<p, q>>
            m   == Head(net[in])
        IN
        /\ net[in] # <<>>
        /\ rcvd' = [rcvd EXCEPT ![p] = @ \cup {m}]
        /\ activeOpens' = activeOpens
        /\ role' = role
        /\ IF state[p] = "LISTEN" /\ m = "SYN" THEN
              /\ state' = [state EXCEPT ![p] = "SYN_RCVD"]
              /\ net' = [net EXCEPT ![in] = Tail(@), ![out] = SendTo(@, "SYNACK")]
           ELSE IF state[p] = "SYN_RCVD" /\ m = "SYN" THEN
              /\ state' = state
              /\ net' = [net EXCEPT ![in] = Tail(@), ![out] = SendTo(@, "SYNACK")]
           ELSE IF state[p] = "SYN_SENT" /\ m = "SYNACK" THEN
              /\ state' = [state EXCEPT ![p] = "ESTABLISHED"]
              /\ net' = [net EXCEPT ![in] = Tail(@), ![out] = SendTo(@, "ACK")]
           ELSE IF state[p] = "ESTABLISHED" /\ m = "SYNACK" THEN
              /\ state' = state
              /\ net' = [net EXCEPT ![in] = Tail(@), ![out] = SendTo(@, "ACK")]
           ELSE IF state[p] = "SYN_RCVD" /\ m = "ACK" THEN
              /\ state' = [state EXCEPT ![p] = "ESTABLISHED"]
              /\ net' = [net EXCEPT ![in] = Tail(@)]
           ELSE
              /\ state' = state
              /\ net' = [net EXCEPT ![in] = Tail(@)]

\* Retransmission (suppressed if an identical copy is already last on the link)
Retransmit(p) ==
    LET out == <<p, Other(p)>> IN
    \/ /\ state[p] = "SYN_SENT"
       /\ CanSend(net[out], "SYN")
       /\ net' = [net EXCEPT ![out] = Append(@, "SYN")]
       /\ UNCHANGED <<state, role, rcvd, activeOpens>>
    \/ /\ state[p] = "SYN_RCVD"
       /\ CanSend(net[out], "SYNACK")
       /\ net' = [net EXCEPT ![out] = Append(@, "SYNACK")]
       /\ UNCHANGED <<state, role, rcvd, activeOpens>>

\* The network may lose messages
Drop ==
    \E c \in Chans :
        /\ net[c] # <<>>
        /\ net' = [net EXCEPT ![c] = Tail(@)]
        /\ UNCHANGED <<state, role, rcvd, activeOpens>>

Next == \/ \E p \in peers : Receive(p) \/ Retransmit(p)
        \/ Drop

Fairness == \A p \in peers : SF_vars(Receive(p)) /\ SF_vars(Retransmit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
TypeOK ==
    /\ state \in [peers -> States]
    /\ role \in [peers -> Roles]
    /\ DOMAIN net = Chans
    /\ \A c \in Chans : net[c] \in Seq(Msgs)
    /\ rcvd \in [peers -> SUBSET Msgs]
    /\ activeOpens \in Nat

\* No two identical adjacent messages on any channel
NoRetransmission ==
    \A c \in Chans : \A i \in 1..(Len(net[c]) - 1) : net[c][i] # net[c][i + 1]

\* Exactly one active open, performed in the initial scenario
SingleActiveOpen ==
    /\ activeOpens = 1
    /\ Cardinality({p \in peers : role[p] = "active"}) = 1

\* Valid per-endpoint state progression
ValidStates ==
    \A p \in peers :
        /\ role[p] = "active"  => state[p] \in {"SYN_SENT", "ESTABLISHED"}
        /\ role[p] = "passive" => state[p] \in {"LISTEN", "SYN_RCVD", "ESTABLISHED"}

\* Correct handshake semantics precede ESTABLISHED (SYN -> SYN-ACK -> ACK)
HandshakeOrder ==
    \A p \in peers :
        state[p] = "ESTABLISHED" =>
            /\ role[p] = "active"  => "SYNACK" \in rcvd[p]
            /\ role[p] = "passive" => {"SYN", "ACK"} \subseteq rcvd[p]

\* Consistency of connection existence between the peers
ConnConsistency ==
    \A p \in peers :
        LET q == Other(p) IN
        /\ (role[p] = "active" /\ state[p] = "ESTABLISHED")
              => state[q] \in {"SYN_RCVD", "ESTABLISHED"}
        /\ (role[p] = "passive" /\ state[p] = "ESTABLISHED")
              => state[q] = "ESTABLISHED"
        /\ (role[p] = "passive" /\ state[p] \in {"SYN_RCVD", "ESTABLISHED"})
              => role[q] = "active"

Inv ==
    /\ TypeOK
    /\ ValidStates
    /\ HandshakeOrder
    /\ ConnConsistency
    /\ NoRetransmission
    /\ SingleActiveOpen

\* Liveness: both endpoints eventually reach and remain in ESTABLISHED
Prop == <>[](\A p \in peers : state[p] = "ESTABLISHED")

=============================================================================
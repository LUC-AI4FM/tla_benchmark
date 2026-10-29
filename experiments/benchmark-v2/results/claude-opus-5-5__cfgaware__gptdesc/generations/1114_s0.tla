---------------------------- MODULE MCtcp ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS A, B

CONSTANT Peers

VARIABLES tcb, connstate, network

vars == <<tcb, connstate, network>>

peers == {A, B}

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "TIME-WAIT",
           "CLOSE-WAIT", "LAST-ACK"}

Segments == {"SYN", "SYN,ACK", "ACK", "FIN", "RST"}

Other(p) == CHOOSE q \in Peers : q # p

\* network[p] is the queue of segments in flight towards peer p.
SendTo(p, msg) == [network EXCEPT ![Other(p)] = Append(@, msg)]

-----------------------------------------------------------------------------
\* User calls

PASSIVE_OPEN(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "LISTEN"]
    /\ UNCHANGED network

ACTIVE_OPEN(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ network' = SendTo(p, "SYN")

SEND(p) ==
    /\ connstate[p] = "LISTEN"
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ network' = SendTo(p, "SYN")
    /\ UNCHANGED tcb

CLOSE(p) ==
    \/ /\ connstate[p] \in {"LISTEN", "SYN-SENT"}
       /\ tcb' = [tcb EXCEPT ![p] = FALSE]
       /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
       /\ UNCHANGED network
    \/ /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
       /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-1"]
       /\ network' = SendTo(p, "FIN")
       /\ UNCHANGED tcb
    \/ /\ connstate[p] = "CLOSE-WAIT"
       /\ connstate' = [connstate EXCEPT ![p] = "LAST-ACK"]
       /\ network' = SendTo(p, "FIN")
       /\ UNCHANGED tcb

\* Retransmission of a SYN while waiting for an answer.
RETRANSMIT(p) ==
    /\ connstate[p] = "SYN-SENT"
    /\ network' = SendTo(p, "SYN")
    /\ UNCHANGED <<tcb, connstate>>

TIMEOUT(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

-----------------------------------------------------------------------------
\* Segment arrival

Transition(p, from, seg) ==
    CASE from = "LISTEN"       /\ seg = "SYN"     -> <<"SYN-RECEIVED", "SYN,ACK">>
      [] from = "SYN-SENT"     /\ seg = "SYN,ACK" -> <<"ESTABLISHED", "ACK">>
      [] from = "SYN-SENT"     /\ seg = "SYN"     -> <<"SYN-RECEIVED", "SYN,ACK">>
      [] from = "SYN-RECEIVED" /\ seg = "ACK"     -> <<"ESTABLISHED", "">>
      [] from = "SYN-RECEIVED" /\ seg = "SYN,ACK" -> <<"ESTABLISHED", "ACK">>
      [] from = "ESTABLISHED"  /\ seg = "FIN"     -> <<"CLOSE-WAIT", "ACK">>
      [] from = "FIN-WAIT-1"   /\ seg = "ACK"     -> <<"FIN-WAIT-2", "">>
      [] from = "FIN-WAIT-1"   /\ seg = "FIN"     -> <<"CLOSING", "ACK">>
      [] from = "FIN-WAIT-2"   /\ seg = "FIN"     -> <<"TIME-WAIT", "ACK">>
      [] from = "CLOSING"      /\ seg = "ACK"     -> <<"TIME-WAIT", "">>
      [] from = "LAST-ACK"     /\ seg = "ACK"     -> <<"CLOSED", "">>
      [] OTHER                                    -> <<from, "">>

RECEIVE(p) ==
    /\ network[p] # <<>>
    /\ LET seg   == Head(network[p])
           t     == Transition(p, connstate[p], seg)
           ns    == t[1]
           reply == t[2]
           rest  == [network EXCEPT ![p] = Tail(@)]
       IN /\ connstate' = [connstate EXCEPT ![p] = ns]
          /\ tcb' = [tcb EXCEPT ![p] = (ns # "CLOSED")]
          /\ network' = IF reply = ""
                          THEN rest
                          ELSE [rest EXCEPT ![Other(p)] = Append(@, reply)]

-----------------------------------------------------------------------------

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

Next ==
    \E p \in Peers :
        \/ PASSIVE_OPEN(p)
        \/ ACTIVE_OPEN(p)
        \/ SEND(p)
        \/ CLOSE(p)
        \/ RETRANSMIT(p)
        \/ TIMEOUT(p)
        \/ RECEIVE(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Peers : WF_vars(TIMEOUT(p))

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Segments)]

Inv ==
    \A p \in Peers : tcb[p] <=> (connstate[p] # "CLOSED")

Prop ==
    \A p \in Peers :
        [](connstate[p] = "TIME-WAIT" => <>(connstate[p] = "CLOSED"))

-----------------------------------------------------------------------------
\* Model-checking wrapper

MCInit ==
    /\ tcb = [p \in Peers |-> TRUE]
    /\ connstate = [p \in Peers |-> IF p = A THEN "SYN-SENT" ELSE "LISTEN"]
    /\ network = [p \in Peers |-> IF p = A THEN <<>> ELSE <<"SYN">>]

\* State constraint: adjacent segments in a queue must differ (no retransmission).
NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

\* Action constraint: after the initial setup, no further active opens,
\* passive opens, or sends are explored.
SingleActiveOpen ==
    \A p \in Peers :
        /\ ~ACTIVE_OPEN(p)
        /\ ~PASSIVE_OPEN(p)
        /\ ~SEND(p)

=============================================================================
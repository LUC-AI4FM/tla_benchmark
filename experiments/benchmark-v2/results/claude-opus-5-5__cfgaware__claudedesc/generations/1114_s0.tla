------------------------------- MODULE MCtcp -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS A, B, Peers

VARIABLES tcb, connstate, network

vars == <<tcb, connstate, network>>

peers == {A, B}

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSE-WAIT", "CLOSING",
           "LAST-ACK", "TIME-WAIT"}

Segments == {"SYN", "SYN,ACK", "ACK", "RST", "FIN"}

Other(p) == CHOOSE q \in Peers \ {p} : TRUE

-----------------------------------------------------------------------------
(* network[p] is the queue of segments in flight towards peer p. *)

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Segments)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

-----------------------------------------------------------------------------
PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "LISTEN"]
    /\ UNCHANGED network

ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ network' = [network EXCEPT ![Other(p)] = Append(@, "SYN")]

Close(p) ==
    \/ /\ connstate[p] \in {"LISTEN", "SYN-SENT"}
       /\ tcb' = [tcb EXCEPT ![p] = FALSE]
       /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
       /\ UNCHANGED network
    \/ /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
       /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-1"]
       /\ network' = [network EXCEPT ![Other(p)] = Append(@, "FIN")]
       /\ UNCHANGED tcb
    \/ /\ connstate[p] = "CLOSE-WAIT"
       /\ connstate' = [connstate EXCEPT ![p] = "LAST-ACK"]
       /\ network' = [network EXCEPT ![Other(p)] = Append(@, "FIN")]
       /\ UNCHANGED tcb

Retransmit(p) ==
    \/ /\ connstate[p] = "SYN-SENT"
       /\ network' = [network EXCEPT ![Other(p)] = Append(@, "SYN")]
       /\ UNCHANGED <<tcb, connstate>>
    \/ /\ connstate[p] = "SYN-RECEIVED"
       /\ network' = [network EXCEPT ![Other(p)] = Append(@, "SYN,ACK")]
       /\ UNCHANGED <<tcb, connstate>>
    \/ /\ connstate[p] \in {"FIN-WAIT-1", "LAST-ACK", "CLOSING"}
       /\ network' = [network EXCEPT ![Other(p)] = Append(@, "FIN")]
       /\ UNCHANGED <<tcb, connstate>>

Timeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

(* Consume the head of p's inbox, move to state ns, and send the segments out. *)
Process(p, ns, out) ==
    /\ connstate' = [connstate EXCEPT ![p] = ns]
    /\ tcb' = [tcb EXCEPT ![p] = (ns # "CLOSED")]
    /\ network' = [network EXCEPT ![p] = Tail(@), ![Other(p)] = @ \o out]

Receive(p) ==
    /\ Len(network[p]) > 0
    /\ LET seg == Head(network[p])
           st  == connstate[p]
       IN CASE st = "CLOSED" /\ seg # "RST"         -> Process(p, "CLOSED", <<"RST">>)
            [] st = "LISTEN" /\ seg = "SYN"         -> Process(p, "SYN-RECEIVED", <<"SYN,ACK">>)
            [] st \notin {"CLOSED", "LISTEN"} /\ seg = "RST"
                                                    -> Process(p, "CLOSED", <<>>)
            [] st = "SYN-SENT" /\ seg = "SYN,ACK"   -> Process(p, "ESTABLISHED", <<"ACK">>)
            [] st = "SYN-SENT" /\ seg = "SYN"       -> Process(p, "SYN-RECEIVED", <<"SYN,ACK">>)
            [] st = "SYN-RECEIVED" /\ seg = "ACK"   -> Process(p, "ESTABLISHED", <<>>)
            [] st = "ESTABLISHED" /\ seg = "FIN"    -> Process(p, "CLOSE-WAIT", <<"ACK">>)
            [] st = "FIN-WAIT-1" /\ seg = "ACK"     -> Process(p, "FIN-WAIT-2", <<>>)
            [] st = "FIN-WAIT-1" /\ seg = "FIN"     -> Process(p, "CLOSING", <<"ACK">>)
            [] st = "FIN-WAIT-2" /\ seg = "FIN"     -> Process(p, "TIME-WAIT", <<"ACK">>)
            [] st = "CLOSING" /\ seg = "ACK"        -> Process(p, "TIME-WAIT", <<>>)
            [] st = "LAST-ACK" /\ seg = "ACK"       -> Process(p, "CLOSED", <<>>)
            [] st = "TIME-WAIT" /\ seg = "FIN"      -> Process(p, "TIME-WAIT", <<"ACK">>)
            [] OTHER                                -> Process(p, st, <<>>)

Next ==
    \E p \in Peers :
        \/ PassiveOpen(p)
        \/ ActiveOpen(p)
        \/ Close(p)
        \/ Retransmit(p)
        \/ Timeout(p)
        \/ Receive(p)

Fairness ==
    \A p \in Peers :
        /\ WF_vars(Receive(p))
        /\ WF_vars(Timeout(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
Inv ==
    \A p \in Peers : tcb[p] <=> (connstate[p] # "CLOSED")

Prop ==
    \A p \in Peers :
        (connstate[p] = "SYN-SENT") ~> (connstate[p] \in {"ESTABLISHED", "CLOSED"})

-----------------------------------------------------------------------------
(* Model-checking configuration *)

MCInit ==
    /\ tcb = [p \in Peers |-> TRUE]
    /\ connstate = [p \in Peers |-> IF p = A THEN "SYN-SENT" ELSE "LISTEN"]
    /\ network = [p \in Peers |-> IF p = A THEN <<>> ELSE <<"SYN">>]

NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

SingleActiveOpen ==
    ~ \E p \in Peers :
        \/ ActiveOpen(p)
        \/ PassiveOpen(p)

Symmetry == Permutations(peers)

=============================================================================
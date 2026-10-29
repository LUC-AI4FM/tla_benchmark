------------------------------- MODULE MCTCP -------------------------------
(***************************************************************************)
(* Model-checking configuration for the TCP connection establishment      *)
(* protocol (three-way handshake) between exactly two peers, A and B.     *)
(* The core protocol behavior of the base TCP module is included here so  *)
(* that the module is self-contained.                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS A, B

ASSUME A # B

VARIABLES tcb,        \* tcb[p]: does peer p have a transmission control block?
          connstate,  \* connstate[p]: TCP connection state of peer p
          network     \* network[p]: queue of segments in flight to peer p

vars == <<tcb, connstate, network>>

Peers == {A, B}

Other(p) == IF p = A THEN B ELSE A

States == { "CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
            "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "TIME-WAIT",
            "CLOSE-WAIT", "LAST-ACK" }

Segments == { "SYN", "SYN,ACK", "ACK", "FIN" }

-----------------------------------------------------------------------------
(* Base TCP protocol                                                        *)
-----------------------------------------------------------------------------

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> << >>]

\* Send segment sequence out (zero or one segment) to the other peer.
SendTo(p, out) ==
    network' = [network EXCEPT ![Other(p)] = @ \o out]

\* User call: passive open.
PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "LISTEN"]
    /\ UNCHANGED network

\* User call: active open (sends SYN).
ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ connstate' = [connstate EXCEPT ![p] = "SYN-SENT"]
    /\ SendTo(p, <<"SYN">>)

\* User call: close.
Close(p) ==
    \/ /\ connstate[p] \in {"LISTEN", "SYN-SENT"}
       /\ tcb' = [tcb EXCEPT ![p] = FALSE]
       /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
       /\ UNCHANGED network
    \/ /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
       /\ connstate' = [connstate EXCEPT ![p] = "FIN-WAIT-1"]
       /\ SendTo(p, <<"FIN">>)
       /\ UNCHANGED tcb
    \/ /\ connstate[p] = "CLOSE-WAIT"
       /\ connstate' = [connstate EXCEPT ![p] = "LAST-ACK"]
       /\ SendTo(p, <<"FIN">>)
       /\ UNCHANGED tcb

\* Retransmission of the most recent control segment.
Retransmit(p) ==
    /\ \/ /\ connstate[p] = "SYN-SENT"
          /\ SendTo(p, <<"SYN">>)
       \/ /\ connstate[p] = "SYN-RECEIVED"
          /\ SendTo(p, <<"SYN,ACK">>)
       \/ /\ connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
          /\ SendTo(p, <<"FIN">>)
    /\ UNCHANGED <<tcb, connstate>>

\* Generic segment processing: peer p consumes segment m at the head of its
\* queue, moves to state s2 and replies with out (zero or one segment).
Process(p, s, m, s2, out) ==
    /\ connstate[p] = s
    /\ network[p] # << >>
    /\ Head(network[p]) = m
    /\ connstate' = [connstate EXCEPT ![p] = s2]
    /\ tcb' = [tcb EXCEPT ![p] = (s2 # "CLOSED")]
    /\ network' = [network EXCEPT ![p] = Tail(@),
                                  ![Other(p)] = @ \o out]

Handles(s, m) ==
    \/ s = "LISTEN"       /\ m = "SYN"
    \/ s = "SYN-SENT"     /\ m \in {"SYN", "SYN,ACK"}
    \/ s = "SYN-RECEIVED" /\ m = "ACK"
    \/ s = "ESTABLISHED"  /\ m = "FIN"
    \/ s = "FIN-WAIT-1"   /\ m \in {"ACK", "FIN"}
    \/ s = "FIN-WAIT-2"   /\ m = "FIN"
    \/ s = "CLOSING"      /\ m = "ACK"
    \/ s = "LAST-ACK"     /\ m = "ACK"

ReceiveSegment(p) ==
    \/ Process(p, "LISTEN",       "SYN",     "SYN-RECEIVED", <<"SYN,ACK">>)
    \/ Process(p, "SYN-SENT",     "SYN,ACK", "ESTABLISHED",  <<"ACK">>)
    \/ Process(p, "SYN-SENT",     "SYN",     "SYN-RECEIVED", <<"SYN,ACK">>)
    \/ Process(p, "SYN-RECEIVED", "ACK",     "ESTABLISHED",  << >>)
    \/ Process(p, "ESTABLISHED",  "FIN",     "CLOSE-WAIT",   <<"ACK">>)
    \/ Process(p, "FIN-WAIT-1",   "ACK",     "FIN-WAIT-2",   << >>)
    \/ Process(p, "FIN-WAIT-1",   "FIN",     "CLOSING",      <<"ACK">>)
    \/ Process(p, "FIN-WAIT-2",   "FIN",     "TIME-WAIT",    <<"ACK">>)
    \/ Process(p, "CLOSING",      "ACK",     "TIME-WAIT",    << >>)
    \/ Process(p, "LAST-ACK",     "ACK",     "CLOSED",       << >>)

\* Segments that are not acceptable in the current state are discarded.
DiscardSegment(p) ==
    /\ network[p] # << >>
    /\ ~Handles(connstate[p], Head(network[p]))
    /\ network' = [network EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<tcb, connstate>>

\* Expiry of the TIME-WAIT timer.
Timeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ connstate' = [connstate EXCEPT ![p] = "CLOSED"]
    /\ UNCHANGED network

User(p) ==
    \/ PassiveOpen(p)
    \/ ActiveOpen(p)
    \/ Close(p)

System(p) ==
    \/ ReceiveSegment(p)
    \/ DiscardSegment(p)
    \/ Timeout(p)
    \/ Retransmit(p)

Next == \E p \in Peers : User(p) \/ System(p)

Fairness ==
    \A p \in Peers :
        /\ WF_vars(ReceiveSegment(p))
        /\ WF_vars(DiscardSegment(p))
        /\ WF_vars(Timeout(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties                                                               *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Segments)]

Inv ==
    \A p \in Peers : tcb[p] <=> (connstate[p] # "CLOSED")

Prop ==
    \A p \in Peers : (connstate[p] = "TIME-WAIT") ~> (connstate[p] = "CLOSED")

-----------------------------------------------------------------------------
(* Model-checking configuration                                             *)
-----------------------------------------------------------------------------

\* Symmetry reduction between A and B (defined but disabled, since it can
\* interfere with liveness checking).
Symmetry == Permutations(Peers)

\* Asymmetric initial state: A has already performed an active open
\* (SYN-SENT with SYN in flight to B), while B waits in LISTEN.
MCInit ==
    /\ tcb = [p \in Peers |-> TRUE]
    /\ connstate = [p \in Peers |-> IF p = A THEN "SYN-SENT" ELSE "LISTEN"]
    /\ network = [p \in Peers |-> IF p = B THEN <<"SYN">> ELSE << >>]

\* State constraint: no two consecutive identical segments in any queue,
\* bounding the state space under unbounded retransmissions.
NoRetransmission ==
    \A p \in Peers :
        \A i \in 1..(Len(network[p]) - 1) :
            network[p][i] # network[p][i + 1]

\* Action constraint: no further active opens after the initial setup,
\* since explicit-state model checking cannot handle infinitely many
\* connections.
SingleActiveOpen ==
    ~ \E p \in Peers : ActiveOpen(p)

MCNext ==
    /\ Next
    /\ SingleActiveOpen
    /\ NoRetransmission'

MCSpec == MCInit /\ [][MCNext]_vars /\ Fairness

=============================================================================
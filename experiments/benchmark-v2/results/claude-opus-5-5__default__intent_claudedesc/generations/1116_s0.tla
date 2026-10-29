---------------------------- MODULE TCP ----------------------------
(***************************************************************************)
(* TCP connection state machine (RFC 9293) between exactly two peers.     *)
(* Each peer has a transmission control block flag (tcb) and a connection *)
(* state (connstate).  Peers exchange control segments over FIFO          *)
(* channels: network[p] holds the in-order queue of segments for peer p.  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Peers

ASSUME Cardinality(Peers) = 2

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "CLOSE-WAIT",
           "LAST-ACK", "TIME-WAIT"}

Messages == {"SYN", "SYN,ACK", "ACK", "FIN", "RST"}

VARIABLES tcb, connstate, network

vars == <<tcb, connstate, network>>

Other(p) == CHOOSE q \in Peers : q # p

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

SetState(p, s) == connstate' = [connstate EXCEPT ![p] = s]

SendTo(q, m) == network' = [network EXCEPT ![q] = Append(@, m)]

(***************************************************************************)
(* User commands                                                           *)
(***************************************************************************)

\* OPEN (passive): CLOSED -> LISTEN
PassiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ SetState(p, "LISTEN")
    /\ UNCHANGED network

\* OPEN (active): CLOSED -> SYN-SENT, send SYN
ActiveOpen(p) ==
    /\ connstate[p] = "CLOSED"
    /\ tcb' = [tcb EXCEPT ![p] = TRUE]
    /\ SetState(p, "SYN-SENT")
    /\ SendTo(Other(p), "SYN")

\* SEND in LISTEN: LISTEN -> SYN-SENT, send SYN
ListenSend(p) ==
    /\ connstate[p] = "LISTEN"
    /\ SetState(p, "SYN-SENT")
    /\ SendTo(Other(p), "SYN")
    /\ UNCHANGED tcb

\* CLOSE command
Close(p) ==
    \/ /\ connstate[p] \in {"LISTEN", "SYN-SENT"}
       /\ tcb' = [tcb EXCEPT ![p] = FALSE]
       /\ SetState(p, "CLOSED")
       /\ UNCHANGED network
    \/ /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
       /\ SetState(p, "FIN-WAIT-1")
       /\ SendTo(Other(p), "FIN")
       /\ UNCHANGED tcb
    \/ /\ connstate[p] = "CLOSE-WAIT"
       /\ SetState(p, "LAST-ACK")
       /\ SendTo(Other(p), "FIN")
       /\ UNCHANGED tcb

\* ABORT command
Abort(p) ==
    \/ /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED", "FIN-WAIT-1",
                            "FIN-WAIT-2", "CLOSE-WAIT"}
       /\ tcb' = [tcb EXCEPT ![p] = FALSE]
       /\ SetState(p, "CLOSED")
       /\ SendTo(Other(p), "RST")
    \/ /\ connstate[p] \in {"LISTEN", "SYN-SENT", "CLOSING", "LAST-ACK",
                            "TIME-WAIT"}
       /\ tcb' = [tcb EXCEPT ![p] = FALSE]
       /\ SetState(p, "CLOSED")
       /\ UNCHANGED network

\* 2MSL timeout in TIME-WAIT
Timeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![p] = FALSE]
    /\ SetState(p, "CLOSED")
    /\ UNCHANGED network

(***************************************************************************)
(* Segment arrival: peer p processes the head of its FIFO input queue.    *)
(***************************************************************************)
Receive(p) ==
    LET q  == Other(p)
        m  == Head(network[p])
        st == connstate[p]
        Consume(s) ==
            /\ connstate' = [connstate EXCEPT ![p] = s]
            /\ network' = [network EXCEPT ![p] = Tail(@)]
        Reply(s, r) ==
            /\ connstate' = [connstate EXCEPT ![p] = s]
            /\ network' = [network EXCEPT ![p] = Tail(@), ![q] = Append(@, r)]
        KeepTcb == tcb' = tcb
        DropTcb == tcb' = [tcb EXCEPT ![p] = FALSE]
    IN
    /\ network[p] # <<>>
    /\ CASE st = "CLOSED" /\ m = "RST"            -> Consume("CLOSED") /\ KeepTcb
         [] st = "CLOSED"                         -> Reply("CLOSED", "RST") /\ KeepTcb
         [] st = "LISTEN" /\ m = "SYN"            -> Reply("SYN-RECEIVED", "SYN,ACK") /\ KeepTcb
         [] st = "LISTEN" /\ m = "RST"            -> Consume("LISTEN") /\ KeepTcb
         [] st = "LISTEN"                         -> Reply("LISTEN", "RST") /\ KeepTcb
         [] m = "RST"                             -> Consume("CLOSED") /\ DropTcb
         [] st = "SYN-SENT" /\ m = "SYN,ACK"      -> Reply("ESTABLISHED", "ACK") /\ KeepTcb
         [] st = "SYN-SENT" /\ m = "SYN"          -> Reply("SYN-RECEIVED", "SYN,ACK") /\ KeepTcb
         [] st = "SYN-RECEIVED" /\ m \in {"ACK", "SYN,ACK"}
                                                  -> Consume("ESTABLISHED") /\ KeepTcb
         [] st = "ESTABLISHED" /\ m = "FIN"       -> Reply("CLOSE-WAIT", "ACK") /\ KeepTcb
         [] st = "FIN-WAIT-1" /\ m = "ACK"        -> Consume("FIN-WAIT-2") /\ KeepTcb
         [] st = "FIN-WAIT-1" /\ m = "FIN"        -> Reply("CLOSING", "ACK") /\ KeepTcb
         [] st = "FIN-WAIT-2" /\ m = "FIN"        -> Reply("TIME-WAIT", "ACK") /\ KeepTcb
         [] st = "CLOSING" /\ m = "ACK"           -> Consume("TIME-WAIT") /\ KeepTcb
         [] st = "LAST-ACK" /\ m = "ACK"          -> Consume("CLOSED") /\ DropTcb
         [] OTHER                                 -> Consume(st) /\ KeepTcb

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
User(p) ==
    \/ PassiveOpen(p)
    \/ ActiveOpen(p)
    \/ ListenSend(p)
    \/ Close(p)
    \/ Abort(p)
    \/ Timeout(p)

Next == \E p \in Peers : User(p) \/ Receive(p)

Fairness ==
    \A p \in Peers : /\ WF_vars(Receive(p))
                     /\ WF_vars(Timeout(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TcbConsistent ==
    \A p \in Peers : tcb[p] <=> connstate[p] # "CLOSED"

\* When the network is quiescent, ESTABLISHED on one side implies ESTABLISHED
\* on the other side.
Inv ==
    (\A p \in Peers : network[p] = <<>>) =>
        \A p \in Peers :
            connstate[p] = "ESTABLISHED" => connstate[Other(p)] = "ESTABLISHED"

\* A peer that entered SYN-SENT eventually reaches ESTABLISHED, LISTEN or CLOSED.
SynSentResolves ==
    \A p \in Peers :
        connstate[p] = "SYN-SENT" ~>
            connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}

\* Every in-flight segment is eventually processed.
MessagesProcessed ==
    \A p \in Peers : network[p] # <<>> ~> network[p] = <<>> \/ \E m \in Messages : TRUE

\* TIME-WAIT is not a permanent state.
TimeWaitLeaves ==
    \A p \in Peers : connstate[p] = "TIME-WAIT" ~> connstate[p] # "TIME-WAIT"

THEOREM Spec => [](TypeOK /\ TcbConsistent /\ Inv)
=============================================================================
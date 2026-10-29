------------------------------- MODULE tcp -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Peers

ASSUME Cardinality(Peers) = 2

VARIABLES
    tcb,        \* tcb[p] : does peer p currently hold a transmission control block
    connstate,  \* connstate[p] : current RFC 9293 state of peer p
    network     \* network[p] : FIFO sequence of segments in flight towards p

vars == <<tcb, connstate, network>>

-----------------------------------------------------------------------------
(* User commands *)
ACTIVE_OPEN  == "ACTIVE_OPEN"
PASSIVE_OPEN == "PASSIVE_OPEN"
SEND         == "SEND"
CLOSE        == "CLOSE"
ABORT        == "ABORT"

UserCommands == {ACTIVE_OPEN, PASSIVE_OPEN, SEND, CLOSE, ABORT}

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING", "CLOSE-WAIT",
           "LAST-ACK", "TIME-WAIT"}

Messages == {"SYN", "SYN,ACK", "ACK", "FIN", "RST"}

NONE == "NONE"

\* Bound on user-initiated segments in flight (keeps the state space finite)
MaxInFlight == 2

Other(p) == CHOOSE q \in Peers : q /= p

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
(* Helpers for user-initiated transitions *)

SetState(p, s) ==
    /\ connstate' = [connstate EXCEPT ![p] = s]
    /\ tcb' = [tcb EXCEPT ![p] = (s /= "CLOSED")]

SendTo(p, m) ==
    LET q == Other(p) IN
    /\ Len(network[q]) < MaxInFlight
    /\ network' = [network EXCEPT ![q] = Append(@, m)]

User(p, cmd) ==
    \/ /\ cmd = PASSIVE_OPEN
       /\ connstate[p] = "CLOSED"
       /\ ~tcb[p]
       /\ SetState(p, "LISTEN")
       /\ UNCHANGED network
    \/ /\ cmd = ACTIVE_OPEN
       /\ connstate[p] = "CLOSED"
       /\ ~tcb[p]
       /\ SetState(p, "SYN-SENT")
       /\ SendTo(p, "SYN")
    \/ /\ cmd = SEND
       /\ connstate[p] = "LISTEN"
       /\ SetState(p, "SYN-SENT")
       /\ SendTo(p, "SYN")
    \/ /\ cmd = CLOSE
       /\ \/ /\ connstate[p] \in {"LISTEN", "SYN-SENT"}
             /\ SetState(p, "CLOSED")
             /\ UNCHANGED network
          \/ /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED"}
             /\ SetState(p, "FIN-WAIT-1")
             /\ SendTo(p, "FIN")
          \/ /\ connstate[p] = "CLOSE-WAIT"
             /\ SetState(p, "LAST-ACK")
             /\ SendTo(p, "FIN")
    \/ /\ cmd = ABORT
       /\ \/ /\ connstate[p] \in {"LISTEN", "SYN-SENT"}
             /\ SetState(p, "CLOSED")
             /\ UNCHANGED network
          \/ /\ connstate[p] \in {"SYN-RECEIVED", "ESTABLISHED", "FIN-WAIT-1",
                                  "FIN-WAIT-2", "CLOSE-WAIT"}
             /\ SetState(p, "CLOSED")
             /\ SendTo(p, "RST")

\* TIME-WAIT expiry (2*MSL timeout)
Timeout(p) ==
    /\ connstate[p] = "TIME-WAIT"
    /\ SetState(p, "CLOSED")
    /\ UNCHANGED network

-----------------------------------------------------------------------------
(* Segment arrival processing *)

R(s, rep) == [st |-> s, rep |-> rep]

Handle(s, m) ==
    CASE s = "CLOSED" ->
            IF m = "RST" THEN R("CLOSED", NONE) ELSE R("CLOSED", "RST")
      [] s = "LISTEN" ->
            CASE m = "SYN" -> R("SYN-RECEIVED", "SYN,ACK")
              [] m \in {"ACK", "SYN,ACK"} -> R("LISTEN", "RST")
              [] OTHER -> R("LISTEN", NONE)
      [] s = "SYN-SENT" ->
            CASE m = "SYN,ACK" -> R("ESTABLISHED", "ACK")
              [] m = "SYN" -> R("SYN-RECEIVED", "SYN,ACK")
              [] m = "RST" -> R("CLOSED", NONE)
              [] m = "ACK" -> R("CLOSED", "RST")
              [] OTHER -> R("SYN-SENT", NONE)
      [] s = "SYN-RECEIVED" ->
            CASE m = "ACK" -> R("ESTABLISHED", NONE)
              [] m = "SYN,ACK" -> R("ESTABLISHED", "ACK")
              [] m = "RST" -> R("CLOSED", NONE)
              [] m = "FIN" -> R("CLOSE-WAIT", "ACK")
              [] m = "SYN" -> R("CLOSED", "RST")
              [] OTHER -> R("SYN-RECEIVED", NONE)
      [] s = "ESTABLISHED" ->
            CASE m = "FIN" -> R("CLOSE-WAIT", "ACK")
              [] m = "RST" -> R("CLOSED", NONE)
              [] m = "SYN" -> R("ESTABLISHED", "ACK")
              [] OTHER -> R("ESTABLISHED", NONE)
      [] s = "FIN-WAIT-1" ->
            CASE m = "ACK" -> R("FIN-WAIT-2", NONE)
              [] m = "FIN" -> R("CLOSING", "ACK")
              [] m = "RST" -> R("CLOSED", NONE)
              [] m = "SYN" -> R("FIN-WAIT-1", "ACK")
              [] OTHER -> R("FIN-WAIT-1", NONE)
      [] s = "FIN-WAIT-2" ->
            CASE m = "FIN" -> R("TIME-WAIT", "ACK")
              [] m = "RST" -> R("CLOSED", NONE)
              [] m = "SYN" -> R("FIN-WAIT-2", "ACK")
              [] OTHER -> R("FIN-WAIT-2", NONE)
      [] s = "CLOSE-WAIT" ->
            CASE m = "RST" -> R("CLOSED", NONE)
              [] m = "SYN" -> R("CLOSE-WAIT", "ACK")
              [] OTHER -> R("CLOSE-WAIT", NONE)
      [] s = "CLOSING" ->
            CASE m = "ACK" -> R("TIME-WAIT", NONE)
              [] m = "RST" -> R("CLOSED", NONE)
              [] m = "SYN" -> R("CLOSING", "ACK")
              [] OTHER -> R("CLOSING", NONE)
      [] s = "LAST-ACK" ->
            CASE m = "ACK" -> R("CLOSED", NONE)
              [] m = "RST" -> R("CLOSED", NONE)
              [] m = "SYN" -> R("LAST-ACK", "ACK")
              [] OTHER -> R("LAST-ACK", NONE)
      [] s = "TIME-WAIT" ->
            CASE m = "RST" -> R("CLOSED", NONE)
              [] m \in {"SYN", "FIN"} -> R("TIME-WAIT", "ACK")
              [] OTHER -> R("TIME-WAIT", NONE)
      [] OTHER -> R(s, NONE)

Receive(p) ==
    /\ network[p] /= <<>>
    /\ LET q == Other(p)
           m == Head(network[p])
           r == Handle(connstate[p], m)
       IN
       /\ connstate' = [connstate EXCEPT ![p] = r.st]
       /\ tcb' = [tcb EXCEPT ![p] = (r.st /= "CLOSED")]
       /\ network' = [network EXCEPT
                        ![p] = Tail(@),
                        ![q] = IF r.rep = NONE THEN @ ELSE Append(@, r.rep)]

-----------------------------------------------------------------------------
Next ==
    \E p \in Peers :
        \/ \E c \in UserCommands : User(p, c)
        \/ Receive(p)
        \/ Timeout(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Peers : WF_vars(Receive(p))
    /\ \A p \in Peers : WF_vars(Timeout(p))

-----------------------------------------------------------------------------
(* Properties *)

Inv ==
    (\A p \in Peers : network[p] = <<>>) =>
        \A p, q \in Peers :
            connstate[p] = "ESTABLISHED" => connstate[q] = "ESTABLISHED"

Prop ==
    \A p \in Peers :
        connstate[p] = "SYN-SENT" ~>
            connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}

=============================================================================
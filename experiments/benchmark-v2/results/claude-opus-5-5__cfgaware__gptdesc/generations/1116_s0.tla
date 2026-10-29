--------------------------------- MODULE tcp ---------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Peers,
    ACTIVE_OPEN,
    PASSIVE_OPEN,
    SEND

ASSUME Cardinality(Peers) = 2

VARIABLES
    tcb,
    connstate,
    network

vars == <<tcb, connstate, network>>

States == {"CLOSED", "LISTEN", "SYN-SENT", "SYN-RECEIVED", "ESTABLISHED",
           "FIN-WAIT-1", "FIN-WAIT-2", "CLOSE-WAIT", "CLOSING",
           "LAST-ACK", "TIME-WAIT"}

Messages == {"SYN", "SYN,ACK", "ACK", "FIN", "RST"}

UserCommands == {ACTIVE_OPEN, PASSIVE_OPEN, SEND}

MaxLen == 3

Other(p) == CHOOSE q \in Peers : q # p

TypeOK ==
    /\ tcb \in [Peers -> BOOLEAN]
    /\ connstate \in [Peers -> States]
    /\ network \in [Peers -> Seq(Messages)]

Init ==
    /\ tcb = [p \in Peers |-> FALSE]
    /\ connstate = [p \in Peers |-> "CLOSED"]
    /\ network = [p \in Peers |-> <<>>]

-----------------------------------------------------------------------------
(* User calls *)

User(l, r, cmd) ==
    \/ /\ cmd = ACTIVE_OPEN
       /\ connstate[l] = "CLOSED"
       /\ Len(network[r]) < MaxLen
       /\ tcb' = [tcb EXCEPT ![l] = TRUE]
       /\ connstate' = [connstate EXCEPT ![l] = "SYN-SENT"]
       /\ network' = [network EXCEPT ![r] = Append(@, "SYN")]
    \/ /\ cmd = PASSIVE_OPEN
       /\ connstate[l] = "CLOSED"
       /\ tcb' = [tcb EXCEPT ![l] = TRUE]
       /\ connstate' = [connstate EXCEPT ![l] = "LISTEN"]
       /\ UNCHANGED network
    \/ /\ cmd = SEND
       /\ connstate[l] = "LISTEN"
       /\ Len(network[r]) < MaxLen
       /\ connstate' = [connstate EXCEPT ![l] = "SYN-SENT"]
       /\ network' = [network EXCEPT ![r] = Append(@, "SYN")]
       /\ UNCHANGED tcb

CloseSynSent(l) ==
    /\ connstate[l] = "SYN-SENT"
    /\ tcb' = [tcb EXCEPT ![l] = FALSE]
    /\ connstate' = [connstate EXCEPT ![l] = "CLOSED"]
    /\ UNCHANGED network

Close(l, r) ==
    \/ CloseSynSent(l)
    \/ /\ connstate[l] = "LISTEN"
       /\ tcb' = [tcb EXCEPT ![l] = FALSE]
       /\ connstate' = [connstate EXCEPT ![l] = "CLOSED"]
       /\ UNCHANGED network
    \/ /\ connstate[l] \in {"SYN-RECEIVED", "ESTABLISHED"}
       /\ Len(network[r]) < MaxLen
       /\ connstate' = [connstate EXCEPT ![l] = "FIN-WAIT-1"]
       /\ network' = [network EXCEPT ![r] = Append(@, "FIN")]
       /\ UNCHANGED tcb
    \/ /\ connstate[l] = "CLOSE-WAIT"
       /\ Len(network[r]) < MaxLen
       /\ connstate' = [connstate EXCEPT ![l] = "LAST-ACK"]
       /\ network' = [network EXCEPT ![r] = Append(@, "FIN")]
       /\ UNCHANGED tcb

(* Reset (abort) applicable in (almost) any state with a TCB. *)
Reset(l, r) ==
    /\ tcb[l]
    /\ connstate[l] # "CLOSED"
    /\ Len(network[r]) < MaxLen
    /\ tcb' = [tcb EXCEPT ![l] = FALSE]
    /\ connstate' = [connstate EXCEPT ![l] = "CLOSED"]
    /\ network' = [network EXCEPT ![r] = Append(@, "RST")]

-----------------------------------------------------------------------------
(* Protocol-driven transitions *)

Step(l, r, consumed, newState, reply) ==
    /\ connstate' = [connstate EXCEPT ![l] = newState]
    /\ tcb' = [tcb EXCEPT ![l] = (newState # "CLOSED")]
    /\ network' = [network EXCEPT ![l] = SubSeq(@, consumed + 1, Len(@)),
                                  ![r] = @ \o reply]

HandledPairs ==
    { <<"LISTEN", "SYN">>, <<"SYN-SENT", "SYN,ACK">>, <<"SYN-SENT", "SYN">>,
      <<"SYN-RECEIVED", "ACK">>, <<"SYN-RECEIVED", "SYN,ACK">>,
      <<"ESTABLISHED", "FIN">>, <<"FIN-WAIT-1", "ACK">>,
      <<"FIN-WAIT-1", "FIN">>, <<"FIN-WAIT-2", "FIN">>,
      <<"CLOSING", "ACK">>, <<"LAST-ACK", "ACK">> }

Receive(l, r) ==
    /\ network[l] # <<>>
    /\ LET m == Head(network[l])
           s == connstate[l]
       IN
       \/ /\ s = "LISTEN" /\ m = "SYN"
          /\ Step(l, r, 1, "SYN-RECEIVED", <<"SYN,ACK">>)
       \/ /\ s = "SYN-SENT" /\ m = "SYN,ACK"
          /\ Step(l, r, 1, "ESTABLISHED", <<"ACK">>)
       \/ /\ s = "SYN-SENT" /\ m = "SYN"
          /\ Step(l, r, 1, "SYN-RECEIVED", <<"SYN,ACK">>)
       \/ /\ s = "SYN-RECEIVED" /\ m = "ACK"
          /\ Step(l, r, 1, "ESTABLISHED", <<>>)
       \/ /\ s = "SYN-RECEIVED" /\ m = "SYN,ACK"
          /\ Step(l, r, 1, "ESTABLISHED", <<"ACK">>)
       \/ /\ s = "ESTABLISHED" /\ m = "FIN"
          /\ Step(l, r, 1, "CLOSE-WAIT", <<"ACK">>)
       \/ /\ s = "FIN-WAIT-1" /\ m = "ACK"
          /\ Step(l, r, 1, "FIN-WAIT-2", <<>>)
       \/ /\ s = "FIN-WAIT-1" /\ m = "FIN"
          /\ Step(l, r, 1, "CLOSING", <<"ACK">>)
       \/ /\ s = "FIN-WAIT-2" /\ m = "FIN"
          /\ Step(l, r, 1, "TIME-WAIT", <<"ACK">>)
       \/ /\ s = "CLOSING" /\ m = "ACK"
          /\ Step(l, r, 1, "TIME-WAIT", <<>>)
       \/ /\ s = "LAST-ACK" /\ m = "ACK"
          /\ Step(l, r, 1, "CLOSED", <<>>)
       \* RST handling
       \/ /\ m = "RST" /\ s \notin {"CLOSED", "LISTEN"}
          /\ Step(l, r, 1, "CLOSED", <<>>)
       \/ /\ m = "RST" /\ s \in {"CLOSED", "LISTEN"}
          /\ network' = [network EXCEPT ![l] = Tail(@)]
          /\ UNCHANGED <<tcb, connstate>>
       \* Segment arriving in CLOSED: respond with RST
       \/ /\ m # "RST" /\ s = "CLOSED"
          /\ network' = [network EXCEPT ![l] = Tail(@), ![r] = Append(@, "RST")]
          /\ UNCHANGED <<tcb, connstate>>
       \* Unexpected segments are dropped
       \/ /\ m # "RST" /\ s # "CLOSED"
          /\ <<s, m>> \notin HandledPairs
          /\ network' = [network EXCEPT ![l] = Tail(@)]
          /\ UNCHANGED <<tcb, connstate>>

(* RFC note: FIN-WAIT-1 may go directly to TIME-WAIT when the FIN is      *)
(* received together with the acknowledgment of our own FIN.             *)
FinWait1Shortcut(l, r) ==
    /\ connstate[l] = "FIN-WAIT-1"
    /\ Len(network[l]) >= 2
    /\ network[l][1] = "ACK"
    /\ network[l][2] = "FIN"
    /\ Step(l, r, 2, "TIME-WAIT", <<"ACK">>)

TimeWaitTimeout(l) ==
    /\ connstate[l] = "TIME-WAIT"
    /\ tcb' = [tcb EXCEPT ![l] = FALSE]
    /\ connstate' = [connstate EXCEPT ![l] = "CLOSED"]
    /\ UNCHANGED network

System ==
    \E l \in Peers :
        \/ Receive(l, Other(l))
        \/ FinWait1Shortcut(l, Other(l))
        \/ TimeWaitTimeout(l)

Next ==
    \/ System
    \/ \E l \in Peers :
        \/ \E cmd \in UserCommands : User(l, Other(l), cmd)
        \/ Close(l, Other(l))
        \/ Reset(l, Other(l))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(System)
    /\ \A p \in Peers : WF_vars(CloseSynSent(p))

-----------------------------------------------------------------------------
(* Properties *)

Inv ==
    \A p, q \in Peers :
        (p # q /\ network[p] = <<>> /\ network[q] = <<>>)
            => (connstate[p] = "ESTABLISHED" <=> connstate[q] = "ESTABLISHED")

Prop ==
    \A p \in Peers :
        connstate[p] = "SYN-SENT"
            ~> connstate[p] \in {"ESTABLISHED", "LISTEN", "CLOSED"}

=============================================================================
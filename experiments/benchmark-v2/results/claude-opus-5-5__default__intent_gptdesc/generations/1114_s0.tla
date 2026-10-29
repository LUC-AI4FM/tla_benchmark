------------------------------- MODULE TCPThreeWayHandshake -------------------------------
(***************************************************************************)
(* Abstract model of the TCP three-way handshake between exactly two      *)
(* peers.  One peer performs an active open (sends SYN), the other a      *)
(* passive open (LISTEN, replies SYN-ACK).  Each direction has a FIFO     *)
(* channel.  Messages may be lost and are retransmitted.  Retransmission  *)
(* is suppressed so that a channel never holds two identical adjacent     *)
(* messages.  Which peer opens actively is chosen nondeterministically,   *)
(* so the specification is symmetric in the identities of the peers.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Peers,     \* the two endpoints
          None       \* a value that is not a peer

ASSUME PeersAssumption == Cardinality(Peers) = 2 /\ None \notin Peers

VARIABLES
    state,         \* state[p] : TCP connection state of peer p
    out,           \* out[p]   : FIFO channel of messages from p to the other peer
    activeOpener,  \* the peer that performed the (single) active open, or None
    events         \* events[p]: history of handshake events at peer p

vars == <<state, out, activeOpener, events>>

-----------------------------------------------------------------------------
States == {"CLOSED", "LISTEN", "SYN_SENT", "SYN_RCVD", "ESTABLISHED"}
Msgs   == {"SYN", "SYNACK", "ACK"}
Events == {"sentSYN", "rcvdSYN", "sentSYNACK", "rcvdSYNACK", "sentACK", "rcvdACK"}

Other(p) == CHOOSE q \in Peers : q # p

Last(s) == s[Len(s)]

\* Append m unless it would duplicate the last message in the channel
Snd(s, m) == IF s # <<>> /\ Last(s) = m THEN s ELSE Append(s, m)

\* Valid per-endpoint state transitions
ValidTransitions ==
    { <<"CLOSED", "LISTEN">>, <<"CLOSED", "SYN_SENT">>,
      <<"LISTEN", "SYN_RCVD">>, <<"SYN_SENT", "ESTABLISHED">>,
      <<"SYN_RCVD", "ESTABLISHED">> }
    \cup { <<s, s>> : s \in States }

-----------------------------------------------------------------------------
TypeOK ==
    /\ state \in [Peers -> States]
    /\ out \in [Peers -> Seq(Msgs)]
    /\ activeOpener \in Peers \cup {None}
    /\ events \in [Peers -> SUBSET Events]

Init ==
    /\ state = [p \in Peers |-> "CLOSED"]
    /\ out = [p \in Peers |-> <<>>]
    /\ activeOpener = None
    /\ events = [p \in Peers |-> {}]

(* Active open: only one active open in the whole run, and the other peer  *)
(* must not have opened actively.                                          *)
ActiveOpen(p) ==
    /\ activeOpener = None
    /\ state[p] = "CLOSED"
    /\ state[Other(p)] \in {"CLOSED", "LISTEN"}
    /\ state' = [state EXCEPT ![p] = "SYN_SENT"]
    /\ out' = [out EXCEPT ![p] = Snd(@, "SYN")]
    /\ activeOpener' = p
    /\ events' = [events EXCEPT ![p] = @ \cup {"sentSYN"}]

(* Passive open: not allowed for the active opener and not allowed if the  *)
(* other peer already listens (exactly one active, one passive peer).      *)
PassiveOpen(p) ==
    /\ state[p] = "CLOSED"
    /\ activeOpener # p
    /\ state[Other(p)] # "LISTEN"
    /\ state' = [state EXCEPT ![p] = "LISTEN"]
    /\ UNCHANGED <<out, activeOpener, events>>

(* Retransmission on timeout; only when it would not duplicate the last   *)
(* message in the channel.                                                 *)
Retransmit(p) ==
    \/ /\ state[p] = "SYN_SENT"
       /\ out[p] = <<>> \/ Last(out[p]) # "SYN"
       /\ out' = [out EXCEPT ![p] = Append(@, "SYN")]
       /\ UNCHANGED <<state, activeOpener, events>>
    \/ /\ state[p] = "SYN_RCVD"
       /\ out[p] = <<>> \/ Last(out[p]) # "SYNACK"
       /\ out' = [out EXCEPT ![p] = Append(@, "SYNACK")]
       /\ UNCHANGED <<state, activeOpener, events>>

(* Peer p receives the head message of the channel from the other peer.   *)
Receive(p) ==
    LET q == Other(p) IN
    /\ out[q] # <<>>
    /\ LET m == Head(out[q]) IN
       CASE state[p] = "LISTEN" /\ m = "SYN" ->
              /\ state' = [state EXCEPT ![p] = "SYN_RCVD"]
              /\ out' = [out EXCEPT ![q] = Tail(@), ![p] = Snd(@, "SYNACK")]
              /\ events' = [events EXCEPT ![p] = @ \cup {"rcvdSYN", "sentSYNACK"}]
              /\ UNCHANGED activeOpener
         [] state[p] = "SYN_SENT" /\ m = "SYNACK" ->
              /\ state' = [state EXCEPT ![p] = "ESTABLISHED"]
              /\ out' = [out EXCEPT ![q] = Tail(@), ![p] = Snd(@, "ACK")]
              /\ events' = [events EXCEPT ![p] = @ \cup {"rcvdSYNACK", "sentACK"}]
              /\ UNCHANGED activeOpener
         [] state[p] = "ESTABLISHED" /\ p = activeOpener /\ m = "SYNACK" ->
              \* our ACK was lost: re-acknowledge (suppressed if duplicate)
              /\ out' = [out EXCEPT ![q] = Tail(@), ![p] = Snd(@, "ACK")]
              /\ UNCHANGED <<state, activeOpener, events>>
         [] state[p] = "SYN_RCVD" /\ m = "ACK" ->
              /\ state' = [state EXCEPT ![p] = "ESTABLISHED"]
              /\ out' = [out EXCEPT ![q] = Tail(@)]
              /\ events' = [events EXCEPT ![p] = @ \cup {"rcvdACK"}]
              /\ UNCHANGED activeOpener
         [] OTHER ->
              \* unexpected / stale message is discarded
              /\ out' = [out EXCEPT ![q] = Tail(@)]
              /\ UNCHANGED <<state, activeOpener, events>>

(* Network loses the head message of p's outgoing channel. *)
Lose(p) ==
    /\ out[p] # <<>>
    /\ out' = [out EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<state, activeOpener, events>>

Open == \E p \in Peers : ActiveOpen(p) \/ PassiveOpen(p)

Next ==
    \/ Open
    \/ \E p \in Peers : Retransmit(p) \/ Receive(p) \/ Lose(p)

Fairness ==
    /\ WF_vars(Open)
    /\ \A p \in Peers : SF_vars(Receive(p))
    /\ \A p \in Peers : SF_vars(Retransmit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* No identical adjacent messages in any channel
NoAdjacentDuplicates ==
    \A p \in Peers : \A i \in 1..(Len(out[p]) - 1) : out[p][i] # out[p][i + 1]

\* At most one active open, and only by the recorded active opener
SingleActiveOpen ==
    /\ \A p \in Peers : "sentSYN" \in events[p] => p = activeOpener
    /\ \A p, q \in Peers : (state[p] = "SYN_SENT" /\ state[q] = "SYN_SENT") => p = q

\* Role consistency of local states
RoleConsistency ==
    \A p \in Peers :
        /\ state[p] = "SYN_SENT" => p = activeOpener
        /\ state[p] \in {"LISTEN", "SYN_RCVD"} => p # activeOpener

\* Established only after correct handshake semantics SYN -> SYN-ACK -> ACK
HandshakeOrder ==
    \A p \in Peers :
        state[p] = "ESTABLISHED" =>
            IF p = activeOpener
            THEN {"sentSYN", "rcvdSYNACK", "sentACK"} \subseteq events[p]
                 /\ {"rcvdSYN", "sentSYNACK"} \subseteq events[Other(p)]
            ELSE {"rcvdSYN", "sentSYNACK", "rcvdACK"} \subseteq events[p]
                 /\ {"sentSYN", "rcvdSYNACK", "sentACK"} \subseteq events[Other(p)]

\* Consistency of connection existence between peers
ConnectionConsistency ==
    \A p \in Peers :
        /\ state[p] = "ESTABLISHED" => state[Other(p)] \in {"SYN_RCVD", "ESTABLISHED"}
        /\ (state[p] = "ESTABLISHED" /\ p # activeOpener)
              => state[Other(p)] = "ESTABLISHED"

Inv ==
    /\ TypeOK
    /\ NoAdjacentDuplicates
    /\ SingleActiveOpen
    /\ RoleConsistency
    /\ HandshakeOrder
    /\ ConnectionConsistency

\* Valid per-endpoint TCP state progression (action property)
ValidProgression ==
    [][\A p \in Peers : <<state[p], state'[p]>> \in ValidTransitions]_vars

\* Once established, stays established
EstablishedStable ==
    [][\A p \in Peers : state[p] = "ESTABLISHED" => state'[p] = "ESTABLISHED"]_vars

(* Liveness: both endpoints eventually (and permanently) established *)
BothEstablished == \A p \in Peers : state[p] = "ESTABLISHED"

Liveness == <>[]BothEstablished

(* Symmetry of the two peers (for TLC symmetry reduction) *)
Symmetry == Permutations(Peers)

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => ValidProgression /\ EstablishedStable
THEOREM Spec => Liveness
=============================================================================
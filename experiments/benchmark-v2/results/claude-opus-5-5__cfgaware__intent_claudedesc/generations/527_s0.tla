---------------------------- MODULE MCSession2 ----------------------------
(***************************************************************************)
(* Model-checking harness for a two-party session protocol ("Session2").   *)
(* The base behavior is included here so the module stands alone and      *)
(* parses on its own. No extra constants, constraints or invariants are    *)
(* added beyond the base protocol's own definitions.                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences

Parties == {"client", "server"}

Msgs == {"open", "openAck", "data", "close", "closeAck"}

MaxData == 2

VARIABLES
    cstate,     \* client session state
    sstate,     \* server session state
    chan,       \* messages in flight: a set of [to, type] records
    sent        \* number of data messages sent in the current session

vars == << cstate, sstate, chan, sent >>

States == {"closed", "opening", "open", "closing"}

Msg(to, t) == [to |-> to, type |-> t]

TypeOK ==
    /\ cstate \in States
    /\ sstate \in {"closed", "open"}
    /\ chan \subseteq [to : Parties, type : Msgs]
    /\ sent \in 0..MaxData

Init ==
    /\ cstate = "closed"
    /\ sstate = "closed"
    /\ chan = {}
    /\ sent = 0

(* Client requests a session *)
ClientOpen ==
    /\ cstate = "closed"
    /\ chan = {}
    /\ cstate' = "opening"
    /\ chan' = chan \cup {Msg("server", "open")}
    /\ sent' = 0
    /\ UNCHANGED sstate

(* Server accepts a session *)
ServerAccept ==
    /\ Msg("server", "open") \in chan
    /\ sstate = "closed"
    /\ sstate' = "open"
    /\ chan' = (chan \ {Msg("server", "open")}) \cup {Msg("client", "openAck")}
    /\ UNCHANGED << cstate, sent >>

(* Client receives acknowledgement *)
ClientEstablished ==
    /\ cstate = "opening"
    /\ Msg("client", "openAck") \in chan
    /\ cstate' = "open"
    /\ chan' = chan \ {Msg("client", "openAck")}
    /\ UNCHANGED << sstate, sent >>

(* Client sends data in an established session *)
ClientSend ==
    /\ cstate = "open"
    /\ sent < MaxData
    /\ Msg("server", "data") \notin chan
    /\ chan' = chan \cup {Msg("server", "data")}
    /\ sent' = sent + 1
    /\ UNCHANGED << cstate, sstate >>

(* Server consumes data *)
ServerRecv ==
    /\ sstate = "open"
    /\ Msg("server", "data") \in chan
    /\ chan' = chan \ {Msg("server", "data")}
    /\ UNCHANGED << cstate, sstate, sent >>

(* Client initiates close *)
ClientClose ==
    /\ cstate = "open"
    /\ Msg("server", "data") \notin chan
    /\ cstate' = "closing"
    /\ chan' = chan \cup {Msg("server", "close")}
    /\ UNCHANGED << sstate, sent >>

(* Server handles close *)
ServerClose ==
    /\ sstate = "open"
    /\ Msg("server", "close") \in chan
    /\ sstate' = "closed"
    /\ chan' = (chan \ {Msg("server", "close")}) \cup {Msg("client", "closeAck")}
    /\ UNCHANGED << cstate, sent >>

(* Client completes close *)
ClientClosed ==
    /\ cstate = "closing"
    /\ Msg("client", "closeAck") \in chan
    /\ cstate' = "closed"
    /\ chan' = chan \ {Msg("client", "closeAck")}
    /\ sent' = 0
    /\ UNCHANGED sstate

Next ==
    \/ ClientOpen
    \/ ServerAccept
    \/ ClientEstablished
    \/ ClientSend
    \/ ServerRecv
    \/ ClientClose
    \/ ServerClose
    \/ ClientClosed

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety: client believes the session is open only if the server does *)
SessionConsistency ==
    cstate = "open" => sstate = "open"

=============================================================================
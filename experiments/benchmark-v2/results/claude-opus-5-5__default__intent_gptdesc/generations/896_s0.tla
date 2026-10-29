------------------------------ MODULE MemoryController ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Clients,      \* finite set of clients
    Addresses,    \* finite address space
    Values,       \* set of storable values
    NoReq,        \* marker: no pending request in a client's slot
    NoResp,       \* marker: no response in a client's response slot
    Ack           \* acknowledgement returned for a completed write

VARIABLES
    mem,          \* mem[a] : value stored at address a
    ctl,          \* ctl[c] \in {"ready", "busy", "done"}
    pending,      \* pending[c] : outstanding request of client c, or NoReq
    resp          \* resp[c]    : response for client c (value / Ack), or NoResp

vars == <<mem, ctl, pending, resp>>

-----------------------------------------------------------------------------
(* Abstract request / response formats                                     *)
-----------------------------------------------------------------------------

ReadReqs  == [op : {"Rd"}, adr : Addresses]
WriteReqs == [op : {"Wr"}, adr : Addresses, val : Values]
Requests  == ReadReqs \cup WriteReqs

Responses == Values \cup {Ack}

Statuses  == {"ready", "busy", "done"}

ASSUME
    /\ Clients # {}
    /\ Addresses # {}
    /\ Values # {}
    /\ NoReq \notin Requests
    /\ Ack \notin Values
    /\ NoResp \notin Responses

-----------------------------------------------------------------------------
(* Type invariant                                                           *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ mem     \in [Addresses -> Values]
    /\ ctl     \in [Clients -> Statuses]
    /\ pending \in [Clients -> Requests \cup {NoReq}]
    /\ resp    \in [Clients -> Responses \cup {NoResp}]

-----------------------------------------------------------------------------
(* Initial state                                                            *)
-----------------------------------------------------------------------------

Init ==
    /\ mem     \in [Addresses -> Values]
    /\ ctl     = [c \in Clients |-> "ready"]
    /\ pending = [c \in Clients |-> NoReq]
    /\ resp    = [c \in Clients |-> NoResp]

-----------------------------------------------------------------------------
(* Transitions                                                              *)
-----------------------------------------------------------------------------

\* The controller accepts a new request from a ready client.
\* Memory and responses are untouched.
Accept(c) ==
    /\ ctl[c] = "ready"
    /\ \E req \in Requests :
          pending' = [pending EXCEPT ![c] = req]
    /\ ctl' = [ctl EXCEPT ![c] = "busy"]
    /\ UNCHANGED <<mem, resp>>

\* The controller atomically performs the pending request of one busy client.
Perform(c) ==
    /\ ctl[c] = "busy"
    /\ LET req == pending[c] IN
         /\ mem' = IF req.op = "Wr"
                     THEN [mem EXCEPT ![req.adr] = req.val]
                     ELSE mem
         /\ resp' = [resp EXCEPT ![c] = IF req.op = "Wr"
                                           THEN Ack
                                           ELSE mem[req.adr]]
    /\ pending' = [pending EXCEPT ![c] = NoReq]
    /\ ctl'     = [ctl EXCEPT ![c] = "done"]

\* The client consumes its response and becomes ready again.
Respond(c) ==
    /\ ctl[c] = "done"
    /\ resp' = [resp EXCEPT ![c] = NoResp]
    /\ ctl'  = [ctl EXCEPT ![c] = "ready"]
    /\ UNCHANGED <<mem, pending>>

Next ==
    \E c \in Clients : Accept(c) \/ Perform(c) \/ Respond(c)

Spec == Init /\ [][Next]_vars

\* Optional fair variant (not required by the description): the controller
\* eventually performs accepted requests and clients eventually consume responses.
FairSpec ==
    /\ Spec
    /\ \A c \in Clients : WF_vars(Perform(c)) /\ WF_vars(Respond(c))

-----------------------------------------------------------------------------
(* Safety invariants                                                        *)
-----------------------------------------------------------------------------

\* Each client has at most one outstanding request, and it exists exactly
\* when the client is busy.
SingleOutstanding ==
    \A c \in Clients :
        /\ (ctl[c] = "busy")  <=> (pending[c] \in Requests)
        /\ (ctl[c] # "busy")  =>  (pending[c] = NoReq)

\* Per-client slots are consistent with the client's status.
SlotConsistency ==
    \A c \in Clients :
        /\ ctl[c] = "ready" => (pending[c] = NoReq /\ resp[c] = NoResp)
        /\ ctl[c] = "busy"  => (pending[c] \in Requests /\ resp[c] = NoResp)
        /\ ctl[c] = "done"  => (pending[c] = NoReq /\ resp[c] \in Responses)

\* Memory remains a total mapping from addresses to values.
MemTotal ==
    /\ DOMAIN mem = Addresses
    /\ \A a \in Addresses : mem[a] \in Values

Inv ==
    /\ TypeOK
    /\ SingleOutstanding
    /\ SlotConsistency
    /\ MemTotal

-----------------------------------------------------------------------------
(* Step (action) properties: memory consistency                             *)
-----------------------------------------------------------------------------

\* Accepting a request never changes memory or responses.
AcceptPreservesMem ==
    [][\A c \in Clients : Accept(c) => UNCHANGED <<mem, resp>>]_vars

\* Responding never changes memory or pending requests.
RespondPreservesMem ==
    [][\A c \in Clients : Respond(c) => UNCHANGED <<mem, pending>>]_vars

\* Memory changes only by performing a write, exactly at the written address.
MemChangesOnlyByWrite ==
    [][ mem' # mem =>
          \E c \in Clients :
              /\ ctl[c] = "busy"
              /\ pending[c] \in WriteReqs
              /\ mem' = [mem EXCEPT ![pending[c].adr] = pending[c].val] ]_vars

\* A performed read returns the current memory value; a performed write
\* returns an acknowledgement.
ResponseCorrect ==
    [][\A c \in Clients :
         Perform(c) =>
            /\ pending[c] \in ReadReqs  => resp'[c] = mem[pending[c].adr]
            /\ pending[c] \in WriteReqs => resp'[c] = Ack ]_vars

\* Only one client is serviced per step (atomic serialization).
OneClientPerStep ==
    [][ Cardinality({c \in Clients :
                        ctl'[c] # ctl[c]}) <= 1 ]_vars

-----------------------------------------------------------------------------
(* Liveness (holds under FairSpec)                                          *)
-----------------------------------------------------------------------------

\* Every accepted request is eventually serviced and the client becomes ready.
RequestsServiced ==
    \A c \in Clients : (ctl[c] = "busy") ~> (ctl[c] = "ready")

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => AcceptPreservesMem /\ RespondPreservesMem
THEOREM Spec => MemChangesOnlyByWrite /\ ResponseCorrect /\ OneClientPerStep
THEOREM FairSpec => RequestsServiced
=============================================================================
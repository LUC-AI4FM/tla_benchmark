--------------------------- MODULE ClientServerQueues ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,      \* set of client processes
    Adr,       \* set of addresses of the replicated service state
    Val,       \* set of data values
    Reg,       \* register/tag constant (opaque identifier for the service)
    Done,      \* reply value returned for a completed write operation
    MaxQLen    \* maximum length of each per-client queue

ASSUME /\ MaxQLen \in Nat \ {0}
       /\ Done \notin Val
       /\ Proc # {}
       /\ Adr # {}
       /\ Val # {}

VARIABLES
    mem,       \* service state: mem[a] is the value stored at address a
    reqQ,      \* reqQ[p]  : pending request queue of client p
    respQ,     \* respQ[p] : replies produced but not yet observed by p
    issued,    \* issued[p]   : number of requests p has enqueued
    served,    \* served[p]   : number of p's requests the server processed
    received,  \* received[p] : number of replies p has observed
    lastReply  \* lastReply[p]: most recent reply observed by p

vars == <<mem, reqQ, respQ, issued, served, received, lastReply>>

-----------------------------------------------------------------------------
Ops == {"rd", "wr"}

Request == [op : Ops, adr : Adr, val : Val, id : Nat]

Reply == [op : Ops, adr : Adr, val : Val \cup {Done}, id : Nat]

NoReply == [op |-> "none", adr |-> "none", val |-> Done, id |-> 0]

MaxIssue == 2 * MaxQLen + 1

-----------------------------------------------------------------------------
Init ==
    /\ mem \in [Adr -> Val]
    /\ reqQ = [p \in Proc |-> << >>]
    /\ respQ = [p \in Proc |-> << >>]
    /\ issued = [p \in Proc |-> 0]
    /\ served = [p \in Proc |-> 0]
    /\ received = [p \in Proc |-> 0]
    /\ lastReply = [p \in Proc |-> NoReply]

\* Client p places a new request into its bounded request queue.
Issue(p) ==
    /\ Len(reqQ[p]) < MaxQLen
    /\ \E op \in Ops, a \in Adr, v \in Val :
          reqQ' = [reqQ EXCEPT ![p] =
                     Append(@, [op |-> op, adr |-> a, val |-> v,
                                id |-> issued[p] + 1])]
    /\ issued' = [issued EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<mem, respQ, served, received, lastReply>>

\* The server dequeues the head request of client p, processes it,
\* and produces the corresponding reply (FIFO per client).
Serve(p) ==
    /\ Len(reqQ[p]) > 0
    /\ Len(respQ[p]) < MaxQLen
    /\ LET req == Head(reqQ[p])
           rep == [op  |-> req.op,
                   adr |-> req.adr,
                   val |-> IF req.op = "rd" THEN mem[req.adr] ELSE Done,
                   id  |-> req.id]
       IN /\ mem' = IF req.op = "wr"
                      THEN [mem EXCEPT ![req.adr] = req.val]
                      ELSE mem
          /\ reqQ' = [reqQ EXCEPT ![p] = Tail(@)]
          /\ respQ' = [respQ EXCEPT ![p] = Append(@, rep)]
    /\ served' = [served EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<issued, received, lastReply>>

\* Client p observes the oldest outstanding reply.
Receive(p) ==
    /\ Len(respQ[p]) > 0
    /\ lastReply' = [lastReply EXCEPT ![p] = Head(respQ[p])]
    /\ respQ' = [respQ EXCEPT ![p] = Tail(@)]
    /\ received' = [received EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<mem, reqQ, issued, served>>

Next == \E p \in Proc : Issue(p) \/ Serve(p) \/ Receive(p)

Fairness == \A p \in Proc : WF_vars(Serve(p)) /\ WF_vars(Receive(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* State constraint bounding the explored state space.
Constraint == \A p \in Proc : issued[p] <= MaxIssue

TypeOK ==
    /\ mem \in [Adr -> Val]
    /\ \A p \in Proc : reqQ[p] \in Seq(Request)
    /\ \A p \in Proc : respQ[p] \in Seq(Reply)
    /\ issued \in [Proc -> Nat]
    /\ served \in [Proc -> Nat]
    /\ received \in [Proc -> Nat]

\* Resource safety: queue lengths never exceed the declared maximum.
QueueBounds ==
    \A p \in Proc : /\ Len(reqQ[p]) <= MaxQLen
                    /\ Len(respQ[p]) <= MaxQLen

\* No loss: every issued request is either pending, has a pending reply,
\* or has had its reply observed.
NoLoss ==
    \A p \in Proc :
        /\ issued[p] = served[p] + Len(reqQ[p])
        /\ served[p] = received[p] + Len(respQ[p])

\* Per-client ordering: pending requests and replies are in issue order.
Ordering ==
    \A p \in Proc :
        /\ \A k \in 1..Len(reqQ[p])  : reqQ[p][k].id  = served[p] + k
        /\ \A k \in 1..Len(respQ[p]) : respQ[p][k].id = received[p] + k
        /\ received[p] > 0 => lastReply[p].id = received[p]

\* Replies match their operation type.
ReplyMatches ==
    \A p \in Proc :
        \A k \in 1..Len(respQ[p]) :
            /\ respQ[p][k].op = "wr" => respQ[p][k].val = Done
            /\ respQ[p][k].op = "rd" => respQ[p][k].val \in Val

DataInvariant ==
    /\ TypeOK
    /\ QueueBounds
    /\ NoLoss
    /\ Ordering
    /\ ReplyMatches

-----------------------------------------------------------------------------
\* Liveness: every enqueued request eventually yields an observed response.
AlwaysResponds ==
    \A p \in Proc :
        \A i \in 1..MaxIssue :
            (issued[p] >= i) ~> (received[p] >= i)

\* Progress: the server does not stall while requests are pending.
Progress ==
    \A p \in Proc :
        (Len(reqQ[p]) > 0) ~> (Len(reqQ[p]) = 0 \/ served[p] > 0)

=============================================================================
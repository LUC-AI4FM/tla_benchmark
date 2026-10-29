------------------------------ MODULE LamportMutex ------------------------------
(***************************************************************************)
(* Timestamp-based distributed mutual exclusion for N asynchronous         *)
(* processes. The algorithm uses Lamport logical clocks and the            *)
(* Ricart-Agrawala request/acknowledgment discipline.                      *)
(*                                                                         *)
(*  - A process requests the critical section (CS) by ticking its clock    *)
(*    and broadcasting a timestamped request.                              *)
(*  - Requests are totally ordered by <<timestamp, process id>>, so ties   *)
(*    on timestamps are broken by process identifier.                      *)
(*  - A receiver acknowledges at once unless it is in the CS or holds an   *)
(*    older (higher-priority) pending request. Otherwise it defers the     *)
(*    acknowledgment until it exits. In this way processes honor requests  *)
(*    with smaller timestamps.                                             *)
(*  - A process enters the CS once every other process has acknowledged.   *)
(*  - The network is reliable but unordered (no FIFO guarantee).           *)
(*    Messages are never lost or duplicated, and processes never crash.    *)
(*                                                                         *)
(* Bounded timestamps: clocks range over 0..MaxClock. Receive and local    *)
(* events saturate at MaxClock. A new request is only allowed while        *)
(* clock < MaxClock. Each request strictly advances the clock, so          *)
(* timestamps of issued requests stay strictly Lamport-ordered and safety  *)
(* and liveness are preserved. Only finitely many requests can be issued.  *)
(* When every process is saturated, idle and the network is empty, the     *)
(* system takes an explicit terminal stuttering step rather than           *)
(* deadlocking.                                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N,          \* number of processes
          MaxClock    \* upper bound on logical clock values

ASSUME NAssump   == N \in Nat \ {0}
ASSUME ClockAssump == MaxClock \in Nat \ {0}

Procs == 1..N

VARIABLES
    clock,     \* clock[p]    : Lamport logical clock of p
    pc,        \* pc[p]       : "idle" | "waiting" | "cs"
    reqTs,     \* reqTs[p]    : timestamp of p's current request (0 if none)
    acks,      \* acks[p]     : processes that acknowledged p's current request
    deferred,  \* deferred[p] : processes whose requests p has deferred
    network    \* set of in-flight messages (unordered, reliable)

vars == <<clock, pc, reqTs, acks, deferred, network>>

-----------------------------------------------------------------------------
(* Helpers *)

MaxOf(a, b) == IF a >= b THEN a ELSE b
MinOf(a, b) == IF a <= b THEN a ELSE b

\* Lamport rule for local events (saturating at the bound)
Tick(c) == MinOf(c + 1, MaxClock)

\* Lamport rule for message receipt: C := max(C, ts) + 1 (saturating)
RecvClock(c, t) == MinOf(MaxOf(c, t) + 1, MaxClock)

\* Total order on requests: timestamps, ties broken by process id
Before(a, b) == \/ a[1] < b[1]
                \/ (a[1] = b[1] /\ a[2] < b[2])

Messages == [type : {"req", "ack"}, from : Procs, to : Procs, ts : 0..MaxClock]

ReqMsg(p, q, t) == [type |-> "req", from |-> p, to |-> q, ts |-> t]
AckMsg(p, q, t) == [type |-> "ack", from |-> p, to |-> q, ts |-> t]

ExactlyOne(s) == Cardinality({i \in DOMAIN s : s[i]}) = 1

-----------------------------------------------------------------------------
TypeOK ==
    /\ clock    \in [Procs -> 0..MaxClock]
    /\ pc       \in [Procs -> {"idle", "waiting", "cs"}]
    /\ reqTs    \in [Procs -> 0..MaxClock]
    /\ acks     \in [Procs -> SUBSET Procs]
    /\ deferred \in [Procs -> SUBSET Procs]
    /\ network  \subseteq Messages

Init ==
    /\ clock    = [p \in Procs |-> 0]
    /\ pc       = [p \in Procs |-> "idle"]
    /\ reqTs    = [p \in Procs |-> 0]
    /\ acks     = [p \in Procs |-> {}]
    /\ deferred = [p \in Procs |-> {}]
    /\ network  = {}

-----------------------------------------------------------------------------
(* Actions *)

\* p issues a new timestamped request and broadcasts it
Request(p) ==
    /\ pc[p] = "idle"
    /\ clock[p] < MaxClock                      \* bounded timestamps
    /\ LET t == clock[p] + 1 IN
         /\ clock'   = [clock EXCEPT ![p] = t]
         /\ reqTs'   = [reqTs EXCEPT ![p] = t]
         /\ pc'      = [pc EXCEPT ![p] = "waiting"]
         /\ acks'    = [acks EXCEPT ![p] = {}]
         /\ network' = network \cup {ReqMsg(p, q, t) : q \in Procs \ {p}}
    /\ UNCHANGED deferred

\* p receives a request m from q. p either acknowledges it or defers it.
ReceiveRequest(p, m) ==
    /\ m \in network
    /\ m.type = "req"
    /\ m.to = p
    /\ LET q     == m.from
           c     == RecvClock(clock[p], m.ts)
           defer == \/ pc[p] = "cs"
                    \/ /\ pc[p] = "waiting"
                       /\ Before(<<reqTs[p], p>>, <<m.ts, q>>)
       IN
         /\ clock' = [clock EXCEPT ![p] = c]
         /\ IF defer
              THEN /\ deferred' = [deferred EXCEPT ![p] = @ \cup {q}]
                   /\ network'  = network \ {m}
              ELSE /\ network'  = (network \ {m}) \cup {AckMsg(p, q, c)}
                   /\ UNCHANGED deferred
    /\ UNCHANGED <<pc, reqTs, acks>>

\* p receives an acknowledgment m
ReceiveAck(p, m) ==
    /\ m \in network
    /\ m.type = "ack"
    /\ m.to = p
    /\ clock'   = [clock EXCEPT ![p] = RecvClock(clock[p], m.ts)]
    /\ acks'    = [acks EXCEPT ![p] = @ \cup {m.from}]
    /\ network' = network \ {m}
    /\ UNCHANGED <<pc, reqTs, deferred>>

Deliver(m) == ReceiveRequest(m.to, m) \/ ReceiveAck(m.to, m)

\* p enters the CS once all other processes have acknowledged
Enter(p) ==
    /\ pc[p] = "waiting"
    /\ acks[p] = Procs \ {p}
    /\ pc'    = [pc EXCEPT ![p] = "cs"]
    /\ clock' = [clock EXCEPT ![p] = Tick(clock[p])]
    /\ UNCHANGED <<reqTs, acks, deferred, network>>

\* p leaves the CS and releases every deferred acknowledgment
Exit(p) ==
    /\ pc[p] = "cs"
    /\ LET c == Tick(clock[p]) IN
         /\ clock'    = [clock EXCEPT ![p] = c]
         /\ network'  = network \cup {AckMsg(p, q, c) : q \in deferred[p]}
    /\ pc'       = [pc EXCEPT ![p] = "idle"]
    /\ reqTs'    = [reqTs EXCEPT ![p] = 0]
    /\ acks'     = [acks EXCEPT ![p] = {}]
    /\ deferred' = [deferred EXCEPT ![p] = {}]

\* Clocks are exhausted and all work is done. This is a legal terminal state
\* reached by stuttering, not a deadlock.
Terminated ==
    /\ \A p \in Procs : pc[p] = "idle" /\ clock[p] = MaxClock
    /\ network = {}
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Request(p) \/ Enter(p) \/ Exit(p)
    \/ \E m \in network : Deliver(m)
    \/ Terminated

\* Fairness assumptions:
\*  - reliable delivery: every sent message is eventually received;
\*  - no crashes: a process whose entry condition holds eventually enters,
\*    and a process in the CS eventually leaves.
\*  - Request has no fairness, because a process may stay idle forever.
Fairness ==
    /\ \A p \in Procs : WF_vars(Enter(p)) /\ WF_vars(Exit(p))
    /\ \A m \in Messages : WF_vars(m \in network /\ Deliver(m))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

ClockBounded == \A p \in Procs : clock[p] <= MaxClock

\* Request bookkeeping is consistent with the control state
RequestStateOK ==
    \A p \in Procs :
        /\ (pc[p] = "idle") => (reqTs[p] = 0 /\ acks[p] = {} /\ deferred[p] = {})
        /\ (pc[p] # "idle") => (reqTs[p] \in 1..clock[p])
        /\ (pc[p] = "cs")   => (acks[p] = Procs \ {p})
        /\ p \notin acks[p]
        /\ p \notin deferred[p]

\* Message delivery semantics
MessageTsBounded ==                 \* a message never carries a future time
    \A m \in network : m.ts <= clock[m.from]

NoSelfMessages == \A m \in network : m.from # m.to

ReqMsgsCurrent ==                   \* in-flight requests belong to live requests
    \A m \in network :
        m.type = "req" => (pc[m.from] = "waiting" /\ m.ts = reqTs[m.from])

AckMsgsCurrent ==                   \* acks are only in flight to waiting requesters
    \A m \in network :
        m.type = "ack" => (pc[m.to] = "waiting" /\ m.from \notin acks[m.to])

\* For every pending request p->q, exactly one of the following holds:
\* the request is in flight, q deferred it, q's ack is in flight, or the ack
\* has been received.
ChannelInvariant ==
    \A p \in Procs : pc[p] = "waiting" =>
      \A q \in Procs \ {p} :
        ExactlyOne(<< ReqMsg(p, q, reqTs[p]) \in network,
                      p \in deferred[q],
                      \E m \in network : m.type = "ack" /\ m.from = q /\ m.to = p,
                      q \in acks[p] >>)

\* An idle process has nothing outstanding anywhere in the system
IdleClean ==
    \A p \in Procs : pc[p] = "idle" =>
        /\ \A m \in network : ~(m.type = "req" /\ m.from = p)
        /\ \A m \in network : ~(m.type = "ack" /\ m.to = p)
        /\ \A q \in Procs : p \notin deferred[q]

\* A deferral happens only for requests with lower priority (or while in the CS)
DeferredValid ==
    \A p \in Procs : \A q \in deferred[p] :
        /\ pc[q] = "waiting"
        /\ \/ pc[p] = "cs"
           \/ /\ pc[p] = "waiting"
              /\ Before(<<reqTs[p], p>>, <<reqTs[q], q>>)

\* Requests with smaller timestamps are honored: the process in the CS holds
\* the highest-priority request among all outstanding requests.
CSHasPriority ==
    \A p, q \in Procs :
        (pc[p] = "cs" /\ pc[q] = "waiting") =>
            Before(<<reqTs[p], p>>, <<reqTs[q], q>>)

Invariants ==
    /\ TypeOK
    /\ MutualExclusion
    /\ ClockBounded
    /\ RequestStateOK
    /\ MessageTsBounded
    /\ NoSelfMessages
    /\ ReqMsgsCurrent
    /\ AckMsgsCurrent
    /\ ChannelInvariant
    /\ IdleClean
    /\ DeferredValid
    /\ CSHasPriority

(* Clock monotonicity and Lamport clock rules, stated as action properties *)

ClockMonotonic ==
    [][\A p \in Procs : clock'[p] >= clock[p]]_vars

RequestAdvancesClock ==
    [][\A p \in Procs :
         (pc[p] = "idle" /\ pc'[p] = "waiting") =>
             (clock'[p] > clock[p] /\ reqTs'[p] = clock'[p])]_vars

ReceiveRule ==                      \* receiver's clock passes the message ts
    [][\A m \in network \ network' :
         clock'[m.to] >= MinOf(m.ts + 1, MaxClock)]_vars

RequestTsStable ==                  \* a request's timestamp never changes
    [][\A p \in Procs :
         (pc[p] # "idle" /\ pc'[p] # "idle") => reqTs'[p] = reqTs[p]]_vars

-----------------------------------------------------------------------------
(* Liveness *)

\* Starvation freedom: every requesting process eventually enters the CS
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "waiting") ~> (pc[p] = "cs")

\* Deadlock freedom: pending requests never get stuck forever
DeadlockFreedom ==
    (\E p \in Procs : pc[p] = "waiting") ~> (\E p \in Procs : pc[p] = "cs")

\* Every process in the CS eventually releases it
EventualRelease ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "idle")

\* Reliable delivery: every message in flight is eventually received
EventualDelivery ==
    \A m \in Messages : (m \in network) ~> (m \notin network)

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => ClockMonotonic /\ RequestAdvancesClock /\ ReceiveRule /\ RequestTsStable
THEOREM Spec => StarvationFreedom /\ DeadlockFreedom /\ EventualRelease /\ EventualDelivery
=============================================================================
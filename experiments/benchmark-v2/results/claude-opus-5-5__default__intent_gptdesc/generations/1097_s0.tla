------------------------------ MODULE LamportMutex ------------------------------
(***************************************************************************)
(* Lamport's distributed mutual-exclusion algorithm.                       *)
(* N processes communicate only through timestamped messages over pairwise *)
(* FIFO channels. Each process has a logical clock that advances when it   *)
(* sends and when it receives messages. There are three message kinds:     *)
(* request (carrying the requester's timestamp), acknowledgement, and      *)
(* release. Channels are bounded so that model checking stays finite.      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,          \* number of processes
    MaxClock,   \* bound on logical clocks (state constraint for TLC)
    MaxChan     \* capacity of every FIFO channel

ASSUME NAssm       == N \in Nat \ {0}
ASSUME MaxClockAssm == MaxClock \in Nat \ {0}
ASSUME MaxChanAssm  == MaxChan \in Nat \ {0}

Proc == 1..N

Max(a, b) == IF a > b THEN a ELSE b

(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
MsgType == {"req", "ack", "rel"}
Message == [type : MsgType, clock : Nat]

ReqMsg(c) == [type |-> "req", clock |-> c]
AckMsg(c) == [type |-> "ack", clock |-> c]
RelMsg(c) == [type |-> "rel", clock |-> c]

VARIABLES
    clock,    \* clock[p]: local logical clock of p
    req,      \* req[p][q]: timestamp of q's outstanding request as known by p (0 = none)
    ack,      \* ack[p]: set of processes that acknowledged p's current request
    network,  \* network[p][q]: FIFO channel of messages from p to q
    crit      \* set of processes currently in the critical section

vars == <<clock, req, ack, network, crit>>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ clock   \in [Proc -> Nat]
    /\ req     \in [Proc -> [Proc -> Nat]]
    /\ ack     \in [Proc -> SUBSET Proc]
    /\ network \in [Proc -> [Proc -> Seq(Message)]]
    /\ \A p, q \in Proc : Len(network[p][q]) <= MaxChan
    /\ crit    \in SUBSET Proc

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ clock   = [p \in Proc |-> 1]
    /\ req     = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ ack     = [p \in Proc |-> {}]
    /\ network = [p \in Proc |-> [q \in Proc |-> << >>]]
    /\ crit    = {}

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
\* Room in every outgoing channel of p (to all peers).
CanBroadcast(p) == \A q \in Proc \ {p} : Len(network[p][q]) < MaxChan

\* Append message m to every channel from p to another process.
Broadcast(p, m) ==
    [network EXCEPT ![p] =
        [q \in Proc |-> IF q = p THEN network[p][q]
                                 ELSE Append(network[p][q], m)]]

\* p's request has priority over q's request in p's local view:
\* lexicographic order on (timestamp, process id).
Beats(p, q) ==
    \/ req[p][q] = 0
    \/ req[p][p] < req[p][q]
    \/ (req[p][p] = req[p][q] /\ p < q)

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* p issues a request: advance clock, record own request, broadcast it.
Request(p) ==
    /\ req[p][p] = 0
    /\ p \notin crit
    /\ clock[p] < MaxClock
    /\ CanBroadcast(p)
    /\ LET c == clock[p] + 1 IN
         /\ clock'   = [clock EXCEPT ![p] = c]
         /\ req'     = [req EXCEPT ![p][p] = c]
         /\ ack'     = [ack EXCEPT ![p] = {p}]
         /\ network' = Broadcast(p, ReqMsg(c))
    /\ UNCHANGED crit

\* p receives a request from q: update clock, record the request, and
\* immediately send an acknowledgement back to q (non-blocking ack).
ReceiveRequest(p, q) ==
    /\ p # q
    /\ network[q][p] # << >>
    /\ LET m == Head(network[q][p])
           c == Max(clock[p], m.clock) + 1
       IN /\ m.type = "req"
          /\ Len(network[p][q]) < MaxChan
          /\ clock'   = [clock EXCEPT ![p] = c]
          /\ req'     = [req EXCEPT ![p][q] = m.clock]
          /\ network' = [network EXCEPT ![q][p] = Tail(network[q][p]),
                                        ![p][q] = Append(network[p][q], AckMsg(c))]
    /\ UNCHANGED <<ack, crit>>

\* p receives an acknowledgement from q.
ReceiveAck(p, q) ==
    /\ p # q
    /\ network[q][p] # << >>
    /\ LET m == Head(network[q][p]) IN
         /\ m.type = "ack"
         /\ clock'   = [clock EXCEPT ![p] = Max(clock[p], m.clock) + 1]
         /\ ack'     = [ack EXCEPT ![p] = @ \cup {q}]
         /\ network' = [network EXCEPT ![q][p] = Tail(network[q][p])]
    /\ UNCHANGED <<req, crit>>

\* p receives a release from q: q's request is removed from p's view.
ReceiveRelease(p, q) ==
    /\ p # q
    /\ network[q][p] # << >>
    /\ LET m == Head(network[q][p]) IN
         /\ m.type = "rel"
         /\ clock'   = [clock EXCEPT ![p] = Max(clock[p], m.clock) + 1]
         /\ req'     = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(network[q][p])]
    /\ UNCHANGED <<ack, crit>>

\* p enters the critical section: all peers acknowledged and p's request
\* has priority over every other outstanding request known to p.
Enter(p) ==
    /\ req[p][p] # 0
    /\ p \notin crit
    /\ ack[p] = Proc
    /\ \A q \in Proc \ {p} : Beats(p, q)
    /\ crit' = crit \cup {p}
    /\ UNCHANGED <<clock, req, ack, network>>

\* p leaves the critical section and broadcasts a release.
Exit(p) ==
    /\ p \in crit
    /\ CanBroadcast(p)
    /\ LET c == clock[p] + 1 IN
         /\ clock'   = [clock EXCEPT ![p] = c]
         /\ network' = Broadcast(p, RelMsg(c))
    /\ crit' = crit \ {p}
    /\ req'  = [req EXCEPT ![p][p] = 0]
    /\ ack'  = [ack EXCEPT ![p] = {}]

Receive(p, q) ==
    \/ ReceiveRequest(p, q)
    \/ ReceiveAck(p, q)
    \/ ReceiveRelease(p, q)

Next ==
    \/ \E p \in Proc : Request(p) \/ Enter(p) \/ Exit(p)
    \/ \E p, q \in Proc : Receive(p, q)

(***************************************************************************)
(* Fairness: fair message delivery and fair scheduling of enter/exit.      *)
(* No fairness on Request: processes are not obliged to request.           *)
(* No crashes are modeled (all processes keep taking steps fairly).        *)
(***************************************************************************)
Fairness ==
    /\ \A p \in Proc :
         /\ WF_vars(Enter(p))
         /\ WF_vars(Exit(p))
    /\ \A p, q \in Proc :
         /\ WF_vars(ReceiveRequest(p, q))
         /\ WF_vars(ReceiveAck(p, q))
         /\ WF_vars(ReceiveRelease(p, q))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* State constraint for TLC to keep the state space finite.                *)
(***************************************************************************)
StateConstraint == \A p \in Proc : clock[p] <= MaxClock + 2 * N

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* Mutual exclusion.
Mutex == \A p, q \in crit : p = q

\* Channels are bounded.
ChannelsBounded == \A p, q \in Proc : Len(network[p][q]) <= MaxChan

\* FIFO + causality: timestamps strictly increase along every channel, and
\* every message in transit carries a timestamp no larger than the
\* sender's current clock.
ChannelTimestampsOrdered ==
    \A p, q \in Proc :
        \A i, j \in DOMAIN network[p][q] :
            i < j => network[p][q][i].clock < network[p][q][j].clock

MessagesCausal ==
    \A p, q \in Proc :
        \A i \in DOMAIN network[p][q] : network[p][q][i].clock <= clock[p]

\* Any request timestamp known to p precedes p's current clock
\* (received or issued events happened before p's present).
KnownRequestsCausal ==
    \A p, q \in Proc : req[p][q] <= clock[p]

\* A process in the critical section has an outstanding request,
\* all acknowledgements, and priority in its own view.
CritWellFormed ==
    \A p \in crit :
        /\ req[p][p] # 0
        /\ ack[p] = Proc
        /\ \A q \in Proc \ {p} : Beats(p, q)

Inv ==
    /\ TypeOK
    /\ Mutex
    /\ ChannelsBounded
    /\ ChannelTimestampsOrdered
    /\ MessagesCausal
    /\ KnownRequestsCausal
    /\ CritWellFormed

\* Logical clock monotonicity: clocks never decrease, and whenever a
\* process sends or receives (its channels change) its clock strictly grows.
ClockMonotonic ==
    [][\A p \in Proc : clock'[p] >= clock[p]]_vars

ClockAdvancesOnCommunication ==
    [][\A p \in Proc :
         (\/ network'[p] # network[p]
          \/ \E q \in Proc : network'[q][p] # network[q][p])
         => clock'[p] > clock[p]]_vars

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

\* Progress: every requesting process eventually enters the critical section.
Progress ==
    \A p \in Proc : (req[p][p] # 0) ~> (p \in crit)

\* Every process in the critical section eventually leaves it.
EventualExit ==
    \A p \in Proc : (p \in crit) ~> (p \notin crit)

\* Non-blocking acknowledgements: a request from q in transit to p
\* eventually results in an acknowledgement from p being sent to q
\* (or already received by q).
RequestInTransit(q, p) ==
    \E i \in DOMAIN network[q][p] : network[q][p][i].type = "req"

AckSentOrReceived(p, q) ==
    \/ p \in ack[q]
    \/ \E i \in DOMAIN network[p][q] : network[p][q][i].type = "ack"

AckEventuallySent ==
    \A p, q \in Proc :
        p # q => (RequestInTransit(q, p) ~> AckSentOrReceived(p, q))

THEOREM Spec => []Inv
THEOREM Spec => ClockMonotonic /\ ClockAdvancesOnCommunication
THEOREM Spec => Progress /\ EventualExit /\ AckEventuallySent
=============================================================================
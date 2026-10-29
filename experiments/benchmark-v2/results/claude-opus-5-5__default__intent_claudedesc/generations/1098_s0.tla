------------------------------ MODULE LamportMutex ------------------------------
(***************************************************************************)
(* Lamport's distributed mutual exclusion algorithm.                       *)
(*                                                                         *)
(* Processes talk over reliable, asynchronous FIFO channels. Each process  *)
(* keeps a Lamport logical clock. A process that wants the critical        *)
(* section (CS) broadcasts a timestamped request and adds it to its own    *)
(* queue. A process that receives a request records it in its queue and    *)
(* replies with a timestamped acknowledgement. A process enters the CS     *)
(* when two conditions hold:                                               *)
(*   - its own request is first in its queue, ordered by                   *)
(*     <<timestamp, process id>>;                                          *)
(*   - it has received acknowledgements from every other process with      *)
(*     timestamps greater than its request's timestamp.                    *)
(* When a process leaves the CS, it removes its request from its queue and *)
(* broadcasts a release message.                                           *)
(*                                                                         *)
(* Model checking: the constant MaxClock bounds the timestamps of new      *)
(* requests. Clocks only increase, so a process can issue only finitely    *)
(* many requests. Each message raises the receiver's clock by a bounded    *)
(* amount, so the reachable state space is finite. Receiving and          *)
(* releasing are never blocked by this bound, so liveness is preserved.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N,          \* number of processes
          MaxClock    \* bound on the logical time at which requests may be issued

ASSUME NAssump        == N \in Nat \ {0}
ASSUME MaxClockAssump == MaxClock \in Nat \ {0}

Proc  == 1 .. N
Clock == Nat

Max(a, b) == IF a >= b THEN a ELSE b

(* Total order on requests: timestamp, ties broken by process id *)
LexLT(a, b) == \/ a[1] < b[1]
               \/ /\ a[1] = b[1]
                  /\ a[2] < b[2]

(* Messages *)
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage(c) == [type |-> "ack", clock |-> c]
RelMessage(c) == [type |-> "rel", clock |-> c]

Message == [type : {"req", "ack", "rel"}, clock : Clock]

VARIABLES
  clock,    \* clock[p]: logical clock of process p
  req,      \* req[p][q]: timestamp of q's pending request as known by p (0 = none)
  ack,      \* ack[p]: processes that acknowledged p's current request
  network,  \* network[p][q]: FIFO channel of messages from p to q
  crit      \* set of processes currently in the critical section

vars == <<clock, req, ack, network, crit>>

-----------------------------------------------------------------------------
TypeOK ==
  /\ clock   \in [Proc -> Clock]
  /\ req     \in [Proc -> [Proc -> Clock]]
  /\ ack     \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit    \in SUBSET Proc

Init ==
  /\ clock   = [p \in Proc |-> 0]
  /\ req     = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack     = [p \in Proc |-> {}]
  /\ network = [p \in Proc |-> [q \in Proc |-> << >>]]
  /\ crit    = {}

-----------------------------------------------------------------------------
(* Send message m from p to every other process *)
Broadcast(p, m) ==
  [q \in Proc |-> IF q = p THEN network[p][q] ELSE Append(network[p][q], m)]

(* p's request is ahead of q's request in p's local queue *)
Beats(p, q) ==
  \/ req[p][q] = 0
  \/ LexLT(<<req[p][p], p>>, <<req[p][q], q>>)

(* Process p requests access to the CS *)
Request(p) ==
  /\ req[p][p] = 0
  /\ p \notin crit
  /\ clock[p] < MaxClock
  /\ LET ts == clock[p] + 1
     IN  /\ clock'   = [clock EXCEPT ![p] = ts]
         /\ req'     = [req EXCEPT ![p][p] = ts]
         /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(ts))]
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED crit

(* Process p receives a request from q and acknowledges it *)
ReceiveRequest(p, q) ==
  /\ q /= p
  /\ network[q][p] /= << >>
  /\ LET m  == Head(network[q][p])
         ts == Max(clock[p], m.clock) + 1
     IN  /\ m.type = "req"
         /\ req'     = [req EXCEPT ![p][q] = m.clock]
         /\ clock'   = [clock EXCEPT ![p] = ts]
         /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                       ![p][q] = Append(@, AckMessage(ts))]
  /\ UNCHANGED <<ack, crit>>

(* Process p receives an acknowledgement from q.                     *)
(* It counts only if its timestamp exceeds p's request timestamp.    *)
ReceiveAck(p, q) ==
  /\ q /= p
  /\ network[q][p] /= << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "ack"
         /\ clock' = [clock EXCEPT ![p] = Max(clock[p], m.clock) + 1]
         /\ ack'   = [ack EXCEPT ![p] =
                        IF req[p][p] /= 0 /\ m.clock > req[p][p]
                          THEN @ \cup {q} ELSE @]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
  /\ UNCHANGED <<req, crit>>

(* Process p receives a release from q and removes q's request from its queue *)
ReceiveRelease(p, q) ==
  /\ q /= p
  /\ network[q][p] /= << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "rel"
         /\ clock'   = [clock EXCEPT ![p] = Max(clock[p], m.clock) + 1]
         /\ req'     = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
  /\ UNCHANGED <<ack, crit>>

(* Process p enters the CS *)
Enter(p) ==
  /\ req[p][p] /= 0
  /\ p \notin crit
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : Beats(p, q)
  /\ crit' = crit \cup {p}
  /\ UNCHANGED <<clock, req, ack, network>>

(* Process p exits the CS and broadcasts a release *)
Exit(p) ==
  /\ p \in crit
  /\ LET ts == clock[p] + 1
     IN  /\ clock'   = [clock EXCEPT ![p] = ts]
         /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage(ts))]
  /\ crit' = crit \ {p}
  /\ req'  = [req EXCEPT ![p][p] = 0]
  /\ ack'  = [ack EXCEPT ![p] = {}]

ReceiveMsg(p) ==
  \E q \in Proc \ {p} :
    \/ ReceiveRequest(p, q)
    \/ ReceiveAck(p, q)
    \/ ReceiveRelease(p, q)

Next ==
  \E p \in Proc :
    \/ Request(p)
    \/ Enter(p)
    \/ Exit(p)
    \/ ReceiveMsg(p)

(* Fairness rules:                                                       *)
(*   - messages are eventually delivered;                                *)
(*   - an enabled entry eventually happens;                              *)
(*   - no process stays in the CS forever.                               *)
(* Requesting the CS is not subject to fairness.                         *)
Fairness ==
  \A p \in Proc :
    /\ WF_vars(ReceiveMsg(p))
    /\ WF_vars(Enter(p))
    /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety: mutual exclusion *)
Mutex == \A p, q \in crit : p = q

(* Fairness (FCFS): a process in the CS holds the earliest pending      *)
(* request, ordered by <<timestamp, process id>>.                       *)
FCFS ==
  \A p \in crit :
    \A q \in Proc \ {p} :
      req[q][q] /= 0 => LexLT(<<req[p][p], p>>, <<req[q][q], q>>)

(* Liveness: every request is eventually granted *)
Liveness == \A p \in Proc : (req[p][p] /= 0) ~> (p \in crit)

(* Deadlock freedom: if someone requests, some process eventually enters *)
DeadlockFreedom ==
  (\E p \in Proc : req[p][p] /= 0) ~> (\E p \in Proc : p \in crit)

(* Optional state constraint for TLC, bounding the clocks *)
ClockConstraint == \A p \in Proc : clock[p] <= MaxClock + 2 * N

THEOREM Spec => []TypeOK /\ []Mutex /\ []FCFS
THEOREM Spec => Liveness /\ DeadlockFreedom
=============================================================================
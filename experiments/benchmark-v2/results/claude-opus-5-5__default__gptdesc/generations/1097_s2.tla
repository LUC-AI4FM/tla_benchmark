------------------------------ MODULE LamportMutex ------------------------------
(***************************************************************************)
(* Lamport's distributed mutual-exclusion algorithm (CACM 1978).           *)
(* Processes communicate over pairwise FIFO channels and use logical       *)
(* clocks, requests, acknowledgements and release messages.                *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N, maxClock

ASSUME NType == N \in Nat
ASSUME maxClockType == maxClock \in Nat

Proc  == 1 .. N
Clock == Nat \ {0}

(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage    == [type |-> "ack", clock |-> 0]
RelMessage    == [type |-> "rel", clock |-> 0]

Message == {AckMessage, RelMessage} \union {ReqMessage(c) : c \in Clock}

VARIABLES
  clock,    \* clock[p]: logical clock of process p
  req,      \* req[p][q]: clock of q's request as known to p (0 = none)
  ack,      \* ack[p]: processes that have acknowledged p's current request
  network,  \* network[p][q]: FIFO channel from p to q
  crit      \* set of processes in the critical section

vars == <<clock, req, ack, network, crit>>

TypeOK ==
  /\ clock \in [Proc -> Clock]
  /\ req \in [Proc -> [Proc -> Nat]]
  /\ ack \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit \in SUBSET Proc

Init ==
  /\ clock = [p \in Proc |-> 1]
  /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack = [p \in Proc |-> {}]
  /\ network = [p \in Proc |-> [q \in Proc |-> << >>]]
  /\ crit = {}

(***************************************************************************)
(* beats(p,q): p's request precedes q's request in p's view.               *)
(***************************************************************************)
beats(p, q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q

\* Append message m to all channels from s to other processes
Broadcast(s, m) ==
  [r \in Proc |-> IF s = r THEN network[s][r] ELSE Append(network[s][r], m)]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Request(p) ==
  /\ req[p][p] = 0
  /\ req' = [req EXCEPT ![p][p] = clock[p]]
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED <<clock, crit>>

ReceiveRequest(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
         c == m.clock
     IN  /\ m.type = "req"
         /\ req' = [req EXCEPT ![p][q] = c]
         /\ clock' = [clock EXCEPT ![p] = IF c > clock[p] THEN c + 1 ELSE @ + 1]
         /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                       ![p][q] = Append(@, AckMessage)]
         /\ UNCHANGED <<ack, crit>>

ReceiveAck(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "ack"
         /\ ack' = [ack EXCEPT ![p] = @ \union {q}]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, req, crit>>

Enter(p) ==
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p, q)
  /\ crit' = crit \union {p}
  /\ UNCHANGED <<clock, req, ack, network>>

Exit(p) ==
  /\ p \in crit
  /\ crit' = crit \ {p}
  /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage)]
  /\ req' = [req EXCEPT ![p][p] = 0]
  /\ ack' = [ack EXCEPT ![p] = {}]
  /\ UNCHANGED clock

ReceiveRelease(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "rel"
         /\ req' = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, ack, crit>>

Next ==
  \/ \E p \in Proc : Request(p) \/ Enter(p) \/ Exit(p)
  \/ \E p \in Proc : \E q \in Proc \ {p} :
        ReceiveRequest(p, q) \/ ReceiveAck(p, q) \/ ReceiveRelease(p, q)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties and model-checking helpers                                   *)
(***************************************************************************)
\* For model checking: bound the number of messages in each channel
BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3

\* State constraint bounding logical clocks
ClockConstraint == \A p \in Proc : clock[p] <= maxClock

\* Mutual exclusion: at most one process is in the critical section
Mutex == \A p, q \in crit : p = q

=============================================================================
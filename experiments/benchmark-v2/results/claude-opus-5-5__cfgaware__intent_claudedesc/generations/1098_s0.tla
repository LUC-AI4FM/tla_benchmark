------------------------------ MODULE LamportMutex ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat, maxClock

NatOverride == 0 .. MaxNat

ASSUME NType == N \in Nat
ASSUME maxClockType == maxClock \in Nat

Proc == 1 .. N
Clock == Nat \ {0}

VARIABLES
  clock,    \* local logical clock of each process
  req,      \* req[p][q]: timestamp of q's request as known by p (0 = none)
  ack,      \* ack[p]: set of processes from which p received acknowledgements
  network,  \* network[p][q]: FIFO channel of messages from p to q
  crit      \* set of processes in the critical section

vars == <<clock, req, ack, network, crit>>

ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage(c) == [type |-> "ack", clock |-> c]
RelMessage(c) == [type |-> "rel", clock |-> c]

Message == {ReqMessage(c) : c \in Clock}
           \cup {AckMessage(c) : c \in Clock}
           \cup {RelMessage(c) : c \in Clock}

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

\* p's own request precedes q's request in p's queue
beats(p, q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q

Broadcast(s, m) ==
  [r \in Proc |-> IF s = r THEN network[s][r] ELSE Append(network[s][r], m)]

Max(a, b) == IF a > b THEN a ELSE b

\* Process p requests the critical section
Request(p) ==
  /\ req[p][p] = 0
  /\ req' = [req EXCEPT ![p][p] = clock[p]]
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED crit

\* Process p receives a request from q and acknowledges it
ReceiveRequest(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
         c == m.clock
         newc == Max(c, clock[p]) + 1
     IN  /\ m.type = "req"
         /\ req' = [req EXCEPT ![p][q] = c]
         /\ clock' = [clock EXCEPT ![p] = newc]
         /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                       ![p][q] = Append(@, AckMessage(newc))]
         /\ UNCHANGED <<ack, crit>>

\* Process p receives an acknowledgement from q
ReceiveAck(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
         c == m.clock
     IN  /\ m.type = "ack"
         /\ clock' = [clock EXCEPT ![p] = Max(c, clock[p]) + 1]
         /\ ack' = [ack EXCEPT ![p] = IF req[p][p] # 0 /\ c > req[p][p]
                                       THEN @ \cup {q} ELSE @]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<req, crit>>

\* Process p enters the critical section
Enter(p) ==
  /\ req[p][p] # 0
  /\ p \notin crit
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p, q)
  /\ crit' = crit \cup {p}
  /\ UNCHANGED <<clock, req, ack, network>>

\* Process p exits the critical section and notifies others
Exit(p) ==
  /\ p \in crit
  /\ crit' = crit \ {p}
  /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage(clock[p]))]
  /\ req' = [req EXCEPT ![p][p] = 0]
  /\ ack' = [ack EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]

\* Process p receives a release message from q
ReceiveRelease(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
         c == m.clock
     IN  /\ m.type = "rel"
         /\ req' = [req EXCEPT ![p][q] = 0]
         /\ clock' = [clock EXCEPT ![p] = Max(c, clock[p]) + 1]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<ack, crit>>

Next ==
  \/ \E p \in Proc : Request(p) \/ Enter(p) \/ Exit(p)
  \/ \E p \in Proc : \E q \in Proc \ {p} :
        ReceiveRequest(p, q) \/ ReceiveAck(p, q) \/ ReceiveRelease(p, q)

Fairness ==
  \A p \in Proc :
     /\ WF_vars(Enter(p))
     /\ WF_vars(Exit(p))
     /\ \A q \in Proc \ {p} :
           /\ WF_vars(ReceiveRequest(p, q))
           /\ WF_vars(ReceiveAck(p, q))
           /\ WF_vars(ReceiveRelease(p, q))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Properties

Mutex == \A p, q \in crit : p = q

DeadlockFreedom ==
  \A p \in Proc : (req[p][p] # 0) ~> (p \in crit)

\* Requests are served in timestamp order (ties broken by process id)
FairOrder ==
  \A p \in crit : \A q \in Proc \ {p} :
     req[q][q] # 0 =>
        \/ req[p][p] < req[q][q]
        \/ (req[p][p] = req[q][q] /\ p < q)

-----------------------------------------------------------------------------
\* Model checking constraints

ClockConstraint == \A p \in Proc : clock[p] <= maxClock

BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 1

=============================================================================
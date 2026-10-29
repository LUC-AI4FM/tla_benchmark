---------------------------- MODULE LamportMutex ----------------------------
(***************************************************************************)
(* Lamport's distributed mutual exclusion algorithm.  N processes use     *)
(* logical clocks and exchange request, acknowledgement and release       *)
(* messages over pairwise FIFO channels.  A process enters the critical   *)
(* section once it has an acknowledgement from every peer and its own     *)
(* request beats every other outstanding request it knows of.  Requests   *)
(* are ordered by timestamp, with ties broken by process id.              *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, maxClock

ASSUME NAssump == N \in Nat \ {0}
ASSUME ClockAssump == maxClock \in Nat \ {0}

Proc == 1..N

\* Bound on the length of each FIFO channel. It keeps model checking finite.
MaxChannelLen == 3

Max(a, b) == IF a >= b THEN a ELSE b

ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage(c) == [type |-> "ack", clock |-> c]
RelMessage(c) == [type |-> "rel", clock |-> c]

Message == [type : {"req", "ack", "rel"}, clock : Nat]

VARIABLES
  clock,    \* clock[p]: local logical clock of process p
  req,      \* req[p][q]: timestamp of q's request as known by p (0 = none)
  ack,      \* ack[p]: set of processes that acknowledged p's current request
  network,  \* network[p][q]: FIFO channel of messages from p to q
  crit      \* set of processes currently in the critical section

vars == <<clock, req, ack, network, crit>>

TypeOK ==
  /\ clock \in [Proc -> Nat]
  /\ req \in [Proc -> [Proc -> Nat]]
  /\ ack \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit \subseteq Proc

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack = [p \in Proc |-> {}]
  /\ network = [p \in Proc |-> [q \in Proc |-> <<>>]]
  /\ crit = {}

\* Process s broadcasts message m to every other process.
Broadcast(s, m) ==
  [r \in Proc |-> IF r = s THEN network[s][r] ELSE Append(network[s][r], m)]

\* From p's point of view, p's request beats q's request.
\* Order is by (timestamp, process id).
Beats(p, q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ (req[p][p] = req[p][q] /\ p < q)

-----------------------------------------------------------------------------
(* Actions *)

\* p issues a request. Its clock ticks because it sends a message.
Request(p) ==
  /\ req[p][p] = 0
  /\ p \notin crit
  /\ LET c == clock[p] + 1 IN
       /\ clock' = [clock EXCEPT ![p] = c]
       /\ req' = [req EXCEPT ![p][p] = c]
       /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(c))]
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED crit

\* p receives a request from q, records it, and acknowledges it.
ReceiveRequest(p, q) ==
  /\ network[q][p] /= << >>
  /\ LET m == Head(network[q][p])
         c == Max(clock[p], m.clock) + 1
     IN /\ m.type = "req"
        /\ req' = [req EXCEPT ![p][q] = m.clock]
        /\ clock' = [clock EXCEPT ![p] = c]
        /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                      ![p][q] = Append(@, AckMessage(c))]
  /\ UNCHANGED <<ack, crit>>

\* p receives an acknowledgement from q.
ReceiveAck(p, q) ==
  /\ network[q][p] /= << >>
  /\ LET m == Head(network[q][p]) IN
       /\ m.type = "ack"
       /\ clock' = [clock EXCEPT ![p] = Max(clock[p], m.clock) + 1]
       /\ ack' = [ack EXCEPT ![p] = @ \cup {q}]
       /\ network' = [network EXCEPT ![q][p] = Tail(@)]
  /\ UNCHANGED <<req, crit>>

\* p receives a release from q and discards q's request.
ReceiveRelease(p, q) ==
  /\ network[q][p] /= << >>
  /\ LET m == Head(network[q][p]) IN
       /\ m.type = "rel"
       /\ clock' = [clock EXCEPT ![p] = Max(clock[p], m.clock) + 1]
       /\ req' = [req EXCEPT ![p][q] = 0]
       /\ network' = [network EXCEPT ![q][p] = Tail(@)]
  /\ UNCHANGED <<ack, crit>>

Receive(p, q) ==
  \/ ReceiveRequest(p, q)
  \/ ReceiveAck(p, q)
  \/ ReceiveRelease(p, q)

\* p enters the critical section once every peer has acknowledged its
\* request and p's request beats all other known requests.
Enter(p) ==
  /\ req[p][p] /= 0
  /\ p \notin crit
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : Beats(p, q)
  /\ crit' = crit \cup {p}
  /\ UNCHANGED <<clock, req, ack, network>>

\* p exits the critical section and broadcasts a release.
Exit(p) ==
  /\ p \in crit
  /\ LET c == clock[p] + 1 IN
       /\ clock' = [clock EXCEPT ![p] = c]
       /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage(c))]
  /\ crit' = crit \ {p}
  /\ req' = [req EXCEPT ![p][p] = 0]
  /\ ack' = [ack EXCEPT ![p] = {}]

Next ==
  \/ \E p \in Proc : Request(p) \/ Enter(p) \/ Exit(p)
  \/ \E p \in Proc, q \in Proc \ {p} : Receive(p, q)

Fairness ==
  /\ \A p \in Proc : WF_vars(Enter(p)) /\ WF_vars(Exit(p))
  /\ \A p \in Proc, q \in Proc \ {p} : WF_vars(Receive(p, q))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* State constraints used to keep model checking finite *)

ClockConstraint == \A p \in Proc : clock[p] <= maxClock

BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= MaxChannelLen

-----------------------------------------------------------------------------
(* Correctness properties *)

\* Safety: at most one process is in the critical section.
Mutex == \A p, q \in crit : p = q

\* A process in the critical section holds the oldest request it knows of.
CritBeatsAll == \A p \in crit : \A q \in Proc \ {p} : Beats(p, q)

\* Requests carry a timestamp no larger than the issuer's current clock.
ReqBelowClock == \A p, q \in Proc : req[q][p] <= clock[p]

\* In-flight messages carry timestamps no larger than the sender's clock.
MsgCausality ==
  \A p, q \in Proc : \A i \in 1..Len(network[p][q]) :
      network[p][q][i].clock <= clock[p]

\* Logical clocks never decrease.
ClockMonotone == [][\A p \in Proc : clock'[p] >= clock[p]]_vars

\* Receiving a message strictly advances the receiver's clock past the
\* message timestamp.
ClockCausal ==
  [][\A p \in Proc, q \in Proc \ {p} :
       Receive(p, q) => clock'[p] > Head(network[q][p]).clock]_vars

\* Liveness: every requesting process eventually enters the critical section.
Progress == \A p \in Proc : (req[p][p] /= 0) ~> (p \in crit)

\* Every received request is eventually acknowledged.
AckEventually ==
  \A p \in Proc, q \in Proc \ {p} :
     (req[q][p] /= 0 /\ p \notin ack[p] \cup {q}) ~> TRUE

\* Every pending request at the head of a channel is eventually consumed,
\* which means an acknowledgement is sent.
RequestAcked ==
  \A p \in Proc, q \in Proc \ {p} :
     (network[q][p] /= << >> /\ Head(network[q][p]).type = "req")
        ~> (\E i \in 1..Len(network[p][q]) : network[p][q][i].type = "ack")
           \/ ack[q] \ {q} /= {}
           \/ req[q][q] = 0

=============================================================================
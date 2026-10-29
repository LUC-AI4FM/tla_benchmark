------------------------------ MODULE LamportMutex ------------------------------
(***************************************************************************)
(* Lamport's distributed mutual-exclusion algorithm.                       *)
(*                                                                         *)
(* N processes coordinate entry to a critical section using Lamport        *)
(* logical clocks. Requests are totally ordered by (timestamp, process id). *)
(* Each pair of processes communicates over a reliable point-to-point      *)
(* channel; no process crashes.                                            *)
(*                                                                         *)
(* Clocks grow without bound in the algorithm. For model checking they are *)
(* bounded by the state constraint ClockConstraint. The standard Nat is    *)
(* replaced by the finite range NatOverride == 0..MaxNat, as configured.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N,        \* number of processes
          maxClock, \* bound on clock values explored by TLC
          MaxNat    \* upper bound of the finite substitute for Nat

ASSUME NAssump == N \in Nat \ {0}
ASSUME ClockAssump == maxClock \in Nat \ {0}

\* Finite replacement for Nat, used via "Nat <- NatOverride" in the config
NatOverride == 0 .. MaxNat

Proc  == 1 .. N
Clock == Nat \ {0}

(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage    == [type |-> "ack", clock |-> 0]
RelMessage    == [type |-> "rel", clock |-> 0]

Message == {AckMessage, RelMessage} \cup {ReqMessage(c) : c \in Clock}

VARIABLES
  clock,    \* clock[p]: local logical clock of process p
  req,      \* req[p][q]: timestamp of q's request as known by p (0 = none)
  ack,      \* ack[p]: set of processes that acknowledged p's current request
  network,  \* network[p][q]: messages in transit from p to q
  crit      \* set of processes currently in the critical section

vars == <<clock, req, ack, network, crit>>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ clock \in [Proc -> Clock]
  /\ req \in [Proc -> [Proc -> Nat]]
  /\ ack \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit \in SUBSET Proc

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ clock = [p \in Proc |-> 1]
  /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack = [p \in Proc |-> {}]
  /\ network = [p \in Proc |-> [q \in Proc |-> << >>]]
  /\ crit = {}

(***************************************************************************)
(* Total order on requests: (timestamp, process id), lexicographic.        *)
(* beats(p, q): from p's point of view, p's request precedes q's.          *)
(***************************************************************************)
beats(p, q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q

\* Send message m from p to every other process
Broadcast(s, m) ==
  [r \in Proc |-> IF s = r THEN network[s][r] ELSE Append(network[s][r], m)]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Local event: the clock advances
Tick(p) ==
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<req, ack, network, crit>>

\* p requests access to the critical section, timestamped with its clock
Request(p) ==
  /\ req[p][p] = 0
  /\ req' = [req EXCEPT ![p][p] = clock[p]]
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED <<clock, crit>>

\* p receives a request from q: record it, update clock, acknowledge
ReceiveRequest(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
         c == m.clock
     IN  /\ m.type = "req"
         /\ req' = [req EXCEPT ![p][q] = c]
         /\ clock' = [clock EXCEPT ![p] = IF c > clock[p] THEN c + 1
                                                         ELSE @ + 1]
         /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                       ![p][q] = Append(@, AckMessage)]
         /\ UNCHANGED <<ack, crit>>

\* p receives an acknowledgement from q
ReceiveAck(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "ack"
         /\ ack' = [ack EXCEPT ![p] = @ \cup {q}]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, req, crit>>

\* p enters the critical section once all processes acknowledged and
\* its request precedes every other pending request it knows of
Enter(p) ==
  /\ req[p][p] # 0
  /\ p \notin crit
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p, q)
  /\ crit' = crit \cup {p}
  /\ UNCHANGED <<clock, req, ack, network>>

\* p leaves the critical section and broadcasts a release
Exit(p) ==
  /\ p \in crit
  /\ crit' = crit \ {p}
  /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage)]
  /\ req' = [req EXCEPT ![p][p] = 0]
  /\ ack' = [ack EXCEPT ![p] = {}]
  /\ UNCHANGED clock

\* p receives a release from q
ReceiveRelease(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "rel"
         /\ req' = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, ack, crit>>

Receive(p) ==
  \E q \in Proc \ {p} :
     ReceiveRequest(p, q) \/ ReceiveAck(p, q) \/ ReceiveRelease(p, q)

Next ==
  \E p \in Proc :
     Tick(p) \/ Request(p) \/ Enter(p) \/ Exit(p) \/ Receive(p)

\* Fairness: message delivery, entry and exit are weakly fair;
\* processes are not forced to tick or to request.
Fairness ==
  \A p \in Proc :
     /\ WF_vars(Receive(p))
     /\ WF_vars(Enter(p))
     /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* State constraints for model checking                                    *)
(***************************************************************************)
ClockConstraint == \A p \in Proc : clock[p] <= maxClock

BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 1

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* Safety: at most one process is in the critical section
Mutex == \A p, q \in crit : p = q

\* Message delivery semantics: no self-messages, at most one outstanding
\* request per sender, and only processes with pending requests are in CS
NoSelfMessages == \A p \in Proc : network[p][p] = << >>

NetworkOK ==
  \A p, q \in Proc :
     \A i \in 1 .. Len(network[p][q]) :
        network[p][q][i].type = "req" => req[p][p] # 0

CritHasRequest == \A p \in crit : req[p][p] # 0 /\ ack[p] = Proc

\* Recorded timestamps never exceed the receiver's clock
ClockBound == \A p, q \in Proc : req[p][q] <= clock[p] \/ q = p

Inv == /\ TypeOK
       /\ Mutex
       /\ NoSelfMessages
       /\ CritHasRequest

\* Clock monotonicity (action property)
ClockMonotonic == [][\A p \in Proc : clock'[p] >= clock[p]]_vars

\* Absence of deadlock: some process with a pending request eventually enters
DeadlockFree ==
  (\E p \in Proc : req[p][p] # 0) ~> (\E p \in Proc : p \in crit)

\* Starvation freedom: every requesting process eventually enters
StarvationFree ==
  \A p \in Proc : (req[p][p] # 0) ~> (p \in crit)

=============================================================================
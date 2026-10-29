---------------------------- MODULE MCLamportMutex ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat, maxClock

ASSUME NAssumption == N \in Nat /\ N > 0
ASSUME MaxNatAssumption == MaxNat \in Nat
ASSUME MaxClockAssumption == maxClock \in Nat

\* Finite stand-in for Nat, substituted for Nat in the TLC configuration.
NatOverride == 0 .. MaxNat

Proc == 1 .. N

VARIABLES clock, req, ack, network, crit

vars == <<clock, req, ack, network, crit>>

ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage == [type |-> "ack", clock |-> 0]
RelMessage == [type |-> "rel", clock |-> 0]

Message == {AckMessage, RelMessage} \cup {ReqMessage(c) : c \in Nat}

TypeOK ==
  /\ clock \in [Proc -> Nat]
  /\ req \in [Proc -> [Proc -> Nat]]
  /\ ack \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit \subseteq Proc

Init ==
  /\ clock = [p \in Proc |-> 1]
  /\ req = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack = [p \in Proc |-> {}]
  /\ network = [p \in Proc |-> [q \in Proc |-> << >>]]
  /\ crit = {}

\* p's request beats q's request (as recorded by p)
beats(p, q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q

Broadcast(s, m) ==
  [r \in Proc |-> IF s = r THEN network[s][r] ELSE Append(network[s][r], m)]

Request(p) ==
  /\ req[p][p] = 0
  /\ req' = [req EXCEPT ![p][p] = clock[p]]
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  /\ ack' = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED <<clock, crit>>

Enter(p) ==
  /\ req[p][p] # 0
  /\ p \notin crit
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p, q)
  /\ crit' = crit \cup {p}
  /\ UNCHANGED <<clock, req, ack, network>>

Exit(p) ==
  /\ p \in crit
  /\ crit' = crit \ {p}
  /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage)]
  /\ req' = [req EXCEPT ![p][p] = 0]
  /\ ack' = [ack EXCEPT ![p] = {}]
  /\ UNCHANGED clock

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
         /\ ack' = [ack EXCEPT ![p] = @ \cup {q}]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, req, crit>>

ReceiveRelease(p, q) ==
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "rel"
         /\ req' = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, ack, crit>>

Receive(p) ==
  \E q \in Proc \ {p} :
     \/ ReceiveRequest(p, q)
     \/ ReceiveAck(p, q)
     \/ ReceiveRelease(p, q)

Next ==
  \E p \in Proc :
     \/ Request(p)
     \/ Enter(p)
     \/ Exit(p)
     \/ Receive(p)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Invariants

BoundedNetwork ==
  \A p, q \in Proc : Len(network[p][q]) <= 3

Mutex ==
  \A p, q \in crit : p = q

\* State constraint for model checking
ClockConstraint ==
  \A p \in Proc : clock[p] <= maxClock

=============================================================================
--------------------------- MODULE MCLamportMutex ---------------------------
(***************************************************************************)
(* Model-checking wrapper for Lamport's distributed mutual exclusion        *)
(* algorithm. N processes coordinate access to a critical section using    *)
(* logical clocks and FIFO message passing, without a central coordinator. *)
(*                                                                         *)
(* The base LamportMutex specification is inlined so this module is       *)
(* self-contained and parses with SANY.                                    *)
(*                                                                         *)
(* Natural numbers are bounded by MaxNat for finite-state model checking.  *)
(* Every use of Nat in the base specification is replaced by MCNat.        *)
(*                                                                         *)
(* Intended TLC configuration:                                             *)
(*   CONSTANTS  N <- MCN    MaxNat <- MCMaxNat    maxClock <- MCMaxClock   *)
(*   SPECIFICATION Spec                                                    *)
(*   CONSTRAINT    ClockConstraint                                         *)
(*   INVARIANTS    TypeOK  BoundedNetwork  Mutex                           *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N, maxClock, MaxNat

ASSUME NAssumption        == N \in Nat \ {0}
ASSUME MaxClockAssumption == maxClock \in Nat \ {0}
ASSUME MaxNatAssumption   == MaxNat \in Nat /\ maxClock < MaxNat

(* Configuration values *)
MCN        == 3
MCMaxNat   == 7
MCMaxClock == 6

(* Bounded override of Nat *)
MCNat == 0 .. MaxNat

Proc  == 1 .. N
Clock == MCNat \ {0}

(* Messages *)
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage    == [type |-> "ack", clock |-> 0]
RelMessage    == [type |-> "rel", clock |-> 0]

Message == {AckMessage, RelMessage} \cup {ReqMessage(c) : c \in Clock}

VARIABLES
  clock,    \* clock[p]: current logical clock of process p
  req,      \* req[p][q]: clock of q's request as known by p (0 if none)
  ack,      \* ack[p]: set of processes that acknowledged p's request
  network,  \* network[p][q]: FIFO channel of messages from p to q
  crit      \* set of processes currently in the critical section

vars == <<clock, req, ack, network, crit>>

-----------------------------------------------------------------------------
Init ==
  /\ clock   = [p \in Proc |-> 1]
  /\ req     = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ ack     = [p \in Proc |-> {}]
  /\ network = [p \in Proc |-> [q \in Proc |-> <<>>]]
  /\ crit    = {}

(* Process p's request beats q's request, according to p's knowledge. *)
beats(p, q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q

(* Send message m from p to every other process. *)
Broadcast(s, m) ==
  [r \in Proc |-> IF s = r THEN network[s][r] ELSE Append(network[s][r], m)]

(* Process p requests access to the critical section. *)
Request(p) ==
  /\ req[p][p] = 0
  /\ req'     = [req EXCEPT ![p][p] = clock[p]]
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  /\ ack'     = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED <<clock, crit>>

(* Process p receives a request from q and acknowledges it. *)
ReceiveRequest(p, q) ==
  /\ network[q][p] # <<>>
  /\ LET m == Head(network[q][p])
         c == m.clock
     IN  /\ m.type = "req"
         /\ req'     = [req EXCEPT ![p][q] = c]
         /\ clock'   = [clock EXCEPT ![p] = IF c > clock[p] THEN c + 1
                                                            ELSE @ + 1]
         /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                       ![p][q] = Append(@, AckMessage)]
         /\ UNCHANGED <<ack, crit>>

(* Process p receives an acknowledgement from q. *)
ReceiveAck(p, q) ==
  /\ network[q][p] # <<>>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "ack"
         /\ ack'     = [ack EXCEPT ![p] = @ \cup {q}]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, req, crit>>

(* Process p enters the critical section. *)
Enter(p) ==
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p, q)
  /\ crit' = crit \cup {p}
  /\ UNCHANGED <<clock, req, ack, network>>

(* Process p exits the critical section and notifies the others. *)
Exit(p) ==
  /\ p \in crit
  /\ crit'    = crit \ {p}
  /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage)]
  /\ req'     = [req EXCEPT ![p][p] = 0]
  /\ ack'     = [ack EXCEPT ![p] = {}]
  /\ UNCHANGED clock

(* Process p receives a release notification from q. *)
ReceiveRelease(p, q) ==
  /\ network[q][p] # <<>>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "rel"
         /\ req'     = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
         /\ UNCHANGED <<clock, ack, crit>>

Next ==
  \/ \E p \in Proc : Request(p) \/ Enter(p) \/ Exit(p)
  \/ \E p \in Proc : \E q \in Proc \ {p} :
        ReceiveRequest(p, q) \/ ReceiveAck(p, q) \/ ReceiveRelease(p, q)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
  /\ clock   \in [Proc -> Clock]
  /\ req     \in [Proc -> [Proc -> MCNat]]
  /\ ack     \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit    \in SUBSET Proc

BoundedNetwork ==
  \A p, q \in Proc : Len(network[p][q]) <= 3

Mutex ==
  \A p, q \in crit : p = q

(* State constraint keeping clock values bounded *)
ClockConstraint ==
  \A p \in Proc : clock[p] <= maxClock

THEOREM Spec => [](TypeOK /\ BoundedNetwork /\ Mutex)
=============================================================================
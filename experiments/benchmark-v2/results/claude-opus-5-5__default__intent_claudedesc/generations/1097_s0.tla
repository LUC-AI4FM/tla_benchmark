---------------------------- MODULE LamportMutex ----------------------------
(***************************************************************************)
(* Lamport's distributed mutual exclusion algorithm, from "Time, Clocks    *)
(* and the Ordering of Events in a Distributed System" (1978).             *)
(*                                                                         *)
(* Processes communicate over point-to-point FIFO channels. Each process  *)
(* keeps a logical clock and a local view of every process's pending      *)
(* request. A request's priority is its timestamp; ties are broken by     *)
(* process identifier.                                                     *)
(*                                                                         *)
(* For model checking, use ClockConstraint as a state constraint. It      *)
(* bounds the logical clocks by MaxClock.                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N, MaxClock

ASSUME NAssumption == N \in Nat \ {0}
ASSUME MaxClockAssumption == MaxClock \in Nat \ {0}

Proc  == 1 .. N
Clock == Nat \ {0}

(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
ReqMessage(c) == [type |-> "req", clock |-> c]
AckMessage    == [type |-> "ack", clock |-> 0]
RelMessage    == [type |-> "rel", clock |-> 0]

Message == {ReqMessage(c) : c \in Clock} \cup {AckMessage, RelMessage}

VARIABLES
  clock,    \* clock[p]: the logical clock of process p
  req,      \* req[p][q]: the timestamp of q's request as known to p (0 = none)
  ack,      \* ack[p]: the set of processes that have acknowledged p's request
  network,  \* network[p][q]: the FIFO channel of messages from p to q
  crit      \* the set of processes currently in the critical section

vars == <<clock, req, ack, network, crit>>

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
(* beats(p, q): according to p's local view, p's own request has priority *)
(* over q's request. This holds if p knows of no request from q, if p's    *)
(* timestamp is lower, or if the timestamps are equal and p's id is lower. *)
(***************************************************************************)
beats(p, q) ==
  \/ req[p][q] = 0
  \/ req[p][p] < req[p][q]
  \/ req[p][p] = req[p][q] /\ p < q

(* Send message m from p to every other process. *)
Broadcast(s, m) ==
  [r \in Proc |-> IF s = r THEN network[s][r] ELSE Append(network[s][r], m)]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

(* Process p broadcasts a request stamped with its current clock. *)
Request(p) ==
  /\ req[p][p] = 0
  /\ req'     = [req EXCEPT ![p][p] = clock[p]]
  /\ network' = [network EXCEPT ![p] = Broadcast(p, ReqMessage(clock[p]))]
  /\ ack'     = [ack EXCEPT ![p] = {p}]
  /\ UNCHANGED <<clock, crit>>

(* Process p receives a request from q. It records the request, updates   *)
(* its logical clock, and sends an acknowledgment to q.                    *)
ReceiveRequest(p, q) ==
  /\ p # q
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
         c == m.clock
     IN  /\ m.type = "req"
         /\ req'     = [req EXCEPT ![p][q] = c]
         /\ clock'   = [clock EXCEPT ![p] = IF c > clock[p] THEN c + 1
                                                            ELSE @ + 1]
         /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                       ![p][q] = Append(@, AckMessage)]
  /\ UNCHANGED <<ack, crit>>

(* Process p receives an acknowledgment from q. *)
ReceiveAck(p, q) ==
  /\ p # q
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "ack"
         /\ ack'     = [ack EXCEPT ![p] = @ \cup {q}]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
  /\ UNCHANGED <<clock, req, crit>>

(* Process p receives a release from q and discards q's request. *)
ReceiveRelease(p, q) ==
  /\ p # q
  /\ network[q][p] # << >>
  /\ LET m == Head(network[q][p])
     IN  /\ m.type = "rel"
         /\ req'     = [req EXCEPT ![p][q] = 0]
         /\ network' = [network EXCEPT ![q][p] = Tail(@)]
  /\ UNCHANGED <<clock, ack, crit>>

(* Process p enters the critical section once two conditions hold:        *)
(* every process has acknowledged its request, and its request beats       *)
(* every other request that p knows about.                                 *)
Enter(p) ==
  /\ p \notin crit
  /\ req[p][p] # 0
  /\ ack[p] = Proc
  /\ \A q \in Proc \ {p} : beats(p, q)
  /\ crit' = crit \cup {p}
  /\ UNCHANGED <<clock, req, ack, network>>

(* Process p leaves the critical section and broadcasts a release. *)
Exit(p) ==
  /\ p \in crit
  /\ crit'    = crit \ {p}
  /\ network' = [network EXCEPT ![p] = Broadcast(p, RelMessage)]
  /\ req'     = [req EXCEPT ![p][p] = 0]
  /\ ack'     = [ack EXCEPT ![p] = {}]
  /\ UNCHANGED clock

Receive(p, q) ==
  \/ ReceiveRequest(p, q)
  \/ ReceiveAck(p, q)
  \/ ReceiveRelease(p, q)

Next ==
  \/ \E p \in Proc : Request(p) \/ Enter(p) \/ Exit(p)
  \/ \E p \in Proc, q \in Proc \ {p} : Receive(p, q)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Fairness. This is optional, for liveness analysis. Message delivery,   *)
(* entry and exit are weakly fair. Requesting is never forced.             *)
(***************************************************************************)
Fairness ==
  /\ \A p \in Proc, q \in Proc \ {p} : WF_vars(Receive(p, q))
  /\ \A p \in Proc : WF_vars(Enter(p)) /\ WF_vars(Exit(p))

FairSpec == Spec /\ Fairness

(***************************************************************************)
(* State constraint for finite-state model checking                       *)
(***************************************************************************)
ClockConstraint == \A p \in Proc : clock[p] <= MaxClock

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
  /\ clock   \in [Proc -> Clock]
  /\ req     \in [Proc -> [Proc -> Nat]]
  /\ ack     \in [Proc -> SUBSET Proc]
  /\ network \in [Proc -> [Proc -> Seq(Message)]]
  /\ crit    \in SUBSET Proc

Mutex == \A p, q \in crit : p = q

BoundedNetwork == \A p, q \in Proc : Len(network[p][q]) <= 3

(***************************************************************************)
(* Liveness property. It is intended for checking under FairSpec, but it  *)
(* may fail when clocks are bounded by the state constraint.               *)
(***************************************************************************)
Liveness == \A p \in Proc : (req[p][p] # 0) ~> (p \in crit)

THEOREM Spec => [](TypeOK /\ Mutex)
=============================================================================
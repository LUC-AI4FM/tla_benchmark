---------------------------- MODULE PartialSynchronyEPFD ----------------------------
(***************************************************************************)
(* A parameterized, partially synchronous distributed system with          *)
(* eventually perfect failure detectors (Chandra and Toueg).               *)
(*                                                                         *)
(* This module is self-contained. It inlines two components:               *)
(*   - Age_Channel: message delivery and message aging (inTransit,         *)
(*     inDelivery). Every in-transit message carries an age that counts    *)
(*     the global ticks since it was sent.                                 *)
(*   - EPFailureDetector: the behavior of correct processes (heartbeats,   *)
(*     waiting times, adaptive timeouts, and suspicion sets).              *)
(*                                                                         *)
(* Encoding of clocks:                                                     *)
(*   The global (environment) clock is never stored as an unbounded        *)
(*   counter. It is encoded only through bounded relative counters:        *)
(*   message ages (bounded by DELTA), process idle times (bounded by PHI), *)
(*   local waiting times (bounded by MaxTimeout+1), and timeouts (bounded  *)
(*   by MaxTimeout). When the parameters are fixed, the state space is     *)
(*   finite, so TLC can check small instances.                             *)
(*                                                                         *)
(* Partial synchrony:                                                      *)
(*   DELTAConstraint: a message is delivered within DELTA ticks.           *)
(*   PHIConstraint:   an alive process takes a step within PHI ticks.      *)
(*   Both are enforced as guards on the Tick action. Time cannot advance   *)
(*   while a constraint would be violated.                                 *)
(*                                                                         *)
(* Note on state explosion: large DELTA, PHI, or MaxTimeout values, and    *)
(* N > 3, make the state space grow very quickly. The aging of every      *)
(* in-transit message, and the per-pair waiting times, dominate.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,          \* number of processes
          T,          \* maximum number of crashed processes
          d0,         \* initial timeout value
          DELTA,      \* bound on message delay (in global ticks)
          PHI,        \* bound on process inactivity (in global ticks)
          MaxTimeout  \* cap on timeouts, which keeps the model finite

ASSUME /\ N \in Nat \ {0}
       /\ T \in 0..N
       /\ DELTA \in Nat \ {0}
       /\ PHI \in Nat \ {0}
       /\ d0 \in Nat
       /\ MaxTimeout \in Nat
       /\ d0 <= MaxTimeout
       \* The cap must be large enough to cover the maximal heartbeat gap.
       /\ MaxTimeout >= 2 * PHI + DELTA

Procs == 1..N

Min(a, b) == IF a <= b THEN a ELSE b

Msg == [from : Procs, age : 0..DELTA]

VARIABLES
  alive,        \* alive[p] : FALSE iff p has crashed
  inTransit,    \* inTransit[r] : set of messages in transit to r (with ages)
  inDelivery,   \* inDelivery[r] : senders whose messages were delivered to r
                \*   and are not yet consumed
  idle,         \* idle[p] : ticks since p's last step (local activity clock)
  suspected,    \* suspected[p] : set of processes that p suspects
  waitingTime,  \* waitingTime[p][q] : p's local time since its last
                \*   heartbeat from q
  timeout       \* timeout[p][q] : p's current timeout for q

chanVars == <<inTransit, inDelivery>>
fdVars   == <<suspected, waitingTime, timeout>>
vars     == <<alive, inTransit, inDelivery, idle, suspected, waitingTime, timeout>>

TypeOK ==
  /\ alive \in [Procs -> BOOLEAN]
  /\ inTransit \in [Procs -> SUBSET Msg]
  /\ inDelivery \in [Procs -> SUBSET Procs]
  /\ idle \in [Procs -> 0..PHI]
  /\ suspected \in [Procs -> SUBSET Procs]
  /\ waitingTime \in [Procs -> [Procs -> 0..(MaxTimeout + 1)]]
  /\ timeout \in [Procs -> [Procs -> 0..MaxTimeout]]

Crashed == {p \in Procs : ~alive[p]}
Correct == {p \in Procs : alive[p]}

-----------------------------------------------------------------------------
Init ==
  /\ alive = [p \in Procs |-> TRUE]
  /\ inTransit = [r \in Procs |-> {}]
  /\ inDelivery = [r \in Procs |-> {}]
  /\ idle = [p \in Procs |-> 0]
  /\ suspected = [p \in Procs |-> {}]
  /\ waitingTime = [p \in Procs |-> [q \in Procs |-> 0]]
  /\ timeout = [p \in Procs |-> [q \in Procs |-> d0]]

-----------------------------------------------------------------------------
(* Environment: crashes *)
Crash(p) ==
  /\ alive[p]
  /\ Cardinality(Crashed) < T
  /\ alive' = [alive EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<inTransit, inDelivery, idle, suspected, waitingTime, timeout>>

(* Age_Channel: deliver an in-transit message to its receiver's buffer *)
Deliver(r, m) ==
  /\ m \in inTransit[r]
  /\ inTransit' = [inTransit EXCEPT ![r] = @ \ {m}]
  /\ inDelivery' = [inDelivery EXCEPT ![r] = @ \cup {m.from}]
  /\ UNCHANGED <<alive, idle, suspected, waitingTime, timeout>>

(* Partial-synchrony constraints that guard the progress of global time *)
DELTAConstraint == \A r \in Procs : \A m \in inTransit[r] : m.age < DELTA
PHIConstraint   == \A p \in Procs : alive[p] => idle[p] < PHI

(* Global clock tick: ages messages and advances local clocks *)
Tick ==
  /\ DELTAConstraint
  /\ PHIConstraint
  /\ inTransit' = [r \in Procs |->
                     {[from |-> m.from, age |-> m.age + 1] : m \in inTransit[r]}]
  /\ idle' = [p \in Procs |-> IF alive[p] THEN idle[p] + 1 ELSE idle[p]]
  /\ waitingTime' = [p \in Procs |-> [q \in Procs |->
                        IF alive[p]
                          THEN Min(waitingTime[p][q] + 1, MaxTimeout + 1)
                          ELSE waitingTime[p][q]]]
  /\ UNCHANGED <<alive, inDelivery, suspected, timeout>>

(* EPFailureDetector: a step of an alive process. It consumes delivered    *)
(* heartbeats, updates suspicions and timeouts, and broadcasts a heartbeat. *)
Step(p) ==
  /\ alive[p]
  /\ LET D == inDelivery[p] IN
       /\ suspected' = [suspected EXCEPT ![p] =
              {q \in Procs \ {p} :
                 IF q \in D
                   THEN FALSE
                   ELSE q \in suspected[p] \/ waitingTime[p][q] > timeout[p][q]}]
       /\ timeout' = [timeout EXCEPT ![p] =
              [q \in Procs |->
                 IF q \in D /\ q \in suspected[p]
                   THEN Min(timeout[p][q] + 1, MaxTimeout)   \* false suspicion
                   ELSE timeout[p][q]]]
       /\ waitingTime' = [waitingTime EXCEPT ![p] =
              [q \in Procs |-> IF q \in D THEN 0 ELSE waitingTime[p][q]]]
  /\ inTransit' = [r \in Procs |->
                     IF r = p THEN inTransit[r]
                              ELSE inTransit[r] \cup {[from |-> p, age |-> 0]}]
  /\ inDelivery' = [inDelivery EXCEPT ![p] = {}]
  /\ idle' = [idle EXCEPT ![p] = 0]
  /\ UNCHANGED alive

Next ==
  \/ \E p \in Procs : Crash(p)
  \/ \E r \in Procs : \E m \in inTransit[r] : Deliver(r, m)
  \/ Tick
  \/ \E p \in Procs : Step(p)

Fairness ==
  /\ WF_vars(Tick)
  /\ \A r \in Procs : WF_vars(\E m \in inTransit[r] : Deliver(r, m))
  /\ \A p \in Procs : WF_vars(Step(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)
CrashBound == Cardinality(Crashed) <= T

NoSelfSuspicion == \A p \in Procs : p \notin suspected[p]

\* Constraints that hold in every reachable state (time never violates them).
AgeBound  == \A r \in Procs : \A m \in inTransit[r] : m.age <= DELTA
IdleBound == \A p \in Procs : alive[p] => idle[p] <= PHI

(* Liveness *)
\* Every crashed process is eventually permanently suspected by every
\* correct process.
StrongCompleteness ==
  <>[](\A p, q \in Procs : (~alive[p] /\ alive[q]) => p \in suspected[q])

\* Eventually, no correct process is suspected by any correct process.
EventuallyStrongAccuracy ==
  <>[](\A p, q \in Procs : (alive[p] /\ alive[q]) => p \notin suspected[q])

THEOREM Spec => [](TypeOK /\ CrashBound /\ NoSelfSuspicion /\ AgeBound /\ IdleBound)
THEOREM Spec => StrongCompleteness /\ EventuallyStrongAccuracy
=============================================================================
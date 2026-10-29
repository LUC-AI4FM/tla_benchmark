---------------------------- MODULE EPFailureDetectorSystem ----------------------------
(***************************************************************************)
(* A parameterized, partially synchronous distributed system equipped with *)
(* an eventually perfect failure detector (<>P), following Chandra and     *)
(* Toueg, "Unreliable Failure Detectors for Reliable Distributed Systems". *)
(*                                                                         *)
(* The original design composes two modules:                               *)
(*   - Age_Channel      : the communication system. It models message      *)
(*                        delivery and message aging.                      *)
(*   - EPFailureDetector: the behavior of correct processes, which send    *)
(*                        heartbeats and maintain timeouts and suspicions. *)
(* Both modules are inlined below so that this module is self-contained.   *)
(* The "Channel" and "Detector" sections mark the composition boundary.    *)
(*                                                                         *)
(* Clocks are encoded so that the state space is finite once the           *)
(* parameters are fixed:                                                   *)
(*   - The global (environment) clock is implicit. Each Tick is one        *)
(*     global time unit. Only relative quantities are stored.              *)
(*   - The age of a message is bounded by DELTA (DELTAConstraint).         *)
(*   - idle[p] counts the ticks since p's last step and is bounded by PHI  *)
(*     (PHIConstraint).                                                    *)
(*   - waiting[p][q] is p's local timer for q and is capped at MaxTimeout. *)
(*   - timeout[p][q] grows adaptively but is capped at MaxTimeout.         *)
(*                                                                         *)
(* Model-checking note: TLC handles small instances, for example N = 2 or  *)
(* N = 3 with T = 1, DELTA = 1, PHI = 1, and a small MaxTimeout. The state *)
(* space grows quickly with DELTA and PHI. Message-age sets range over     *)
(* SUBSET 0..DELTA for every channel, and idle and waiting counters        *)
(* multiply that space. The DELTA constraint in particular causes state    *)
(* explosion.                                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,            \* number of processes
    T,            \* maximum number of processes that may crash
    DELTA,        \* bound on message delay (in global ticks)
    PHI,          \* bound on process inactivity (in global ticks)
    InitTimeout,  \* initial timeout for each monitored process
    MaxTimeout    \* cap on adaptive timeouts and timers (keeps the model finite)

ASSUME /\ N \in Nat \ {0}
       /\ T \in 0..N
       /\ DELTA \in Nat \ {0}
       /\ PHI \in Nat \ {0}
       /\ InitTimeout \in Nat \ {0}
       /\ MaxTimeout \in Nat
       /\ InitTimeout <= MaxTimeout
       \* The cap must leave room for a timeout larger than the true bound.
       /\ MaxTimeout > DELTA + PHI

Procs == 1..N

Min(a, b) == IF a <= b THEN a ELSE b

VARIABLES
    alive,      \* alive[p]: p has not crashed
    msgs,       \* msgs[s][r]: set of ages of heartbeats in transit from s to r
    idle,       \* idle[p]: global ticks since p last took a step
    waiting,    \* waiting[p][q]: p's local timer since p last heard from q
    timeout,    \* timeout[p][q]: p's current timeout for q
    suspected   \* suspected[p]: set of processes that p currently suspects

vars == <<alive, msgs, idle, waiting, timeout, suspected>>

chanVars == <<msgs>>
fdVars   == <<waiting, timeout, suspected>>

TypeOK ==
    /\ alive \in [Procs -> BOOLEAN]
    /\ msgs \in [Procs -> [Procs -> SUBSET (0..DELTA)]]
    /\ idle \in [Procs -> 0..PHI]
    /\ waiting \in [Procs -> [Procs -> 0..MaxTimeout]]
    /\ timeout \in [Procs -> [Procs -> 1..MaxTimeout]]
    /\ suspected \in [Procs -> SUBSET Procs]

Crashed == {p \in Procs : ~alive[p]}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Partial-synchrony constraints. Global time may advance only when both   *)
(* constraints hold.                                                       *)
(***************************************************************************)

\* No message to a live receiver may become older than DELTA.
DELTAConstraint ==
    \A s, r \in Procs : alive[r] => DELTA \notin msgs[s][r]

\* No live process may stay inactive for more than PHI ticks.
PHIConstraint ==
    \A p \in Procs : alive[p] => idle[p] < PHI

-----------------------------------------------------------------------------
Init ==
    /\ alive = [p \in Procs |-> TRUE]
    /\ msgs = [s \in Procs |-> [r \in Procs |-> {}]]
    /\ idle = [p \in Procs |-> 0]
    /\ waiting = [p \in Procs |-> [q \in Procs |-> 0]]
    /\ timeout = [p \in Procs |-> [q \in Procs |-> InitTimeout]]
    /\ suspected = [p \in Procs |-> {}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Environment: a global clock tick (Age_Channel aging and local clocks).  *)
(* Every in-transit message ages by one. Every live process becomes one    *)
(* tick more idle. Every live process's timers advance.                    *)
(***************************************************************************)
Tick ==
    /\ DELTAConstraint
    /\ PHIConstraint
    /\ msgs' = [s \in Procs |-> [r \in Procs |-> {a + 1 : a \in msgs[s][r]}]]
    /\ idle' = [p \in Procs |-> IF alive[p] THEN idle[p] + 1 ELSE idle[p]]
    /\ waiting' = [p \in Procs |-> [q \in Procs |->
                     IF alive[p] THEN Min(waiting[p][q] + 1, MaxTimeout)
                                 ELSE waiting[p][q]]]
    /\ UNCHANGED <<alive, timeout, suspected>>

(***************************************************************************)
(* Environment: process p crashes, if fewer than T processes have crashed. *)
(* Messages addressed to p are lost. Messages p already sent remain in     *)
(* transit and may still be delivered.                                     *)
(***************************************************************************)
Crash(p) ==
    /\ alive[p]
    /\ Cardinality(Crashed) < T
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ msgs' = [s \in Procs |-> [r \in Procs |->
                  IF r = p THEN {} ELSE msgs[s][r]]]
    /\ UNCHANGED <<idle, waiting, timeout, suspected>>

(***************************************************************************)
(* Process step (EPFailureDetector). A live process p does the following   *)
(* atomically:                                                             *)
(*   1. Receives every heartbeat addressed to it (Age_Channel delivery).   *)
(*   2. For each q it heard from: resets its timer for q. If it wrongly    *)
(*      suspected q, it removes q and increases its timeout for q.         *)
(*   3. For each q it did not hear from: suspects q if its timer has       *)
(*      reached the timeout.                                               *)
(*   4. Sends a heartbeat to every other live process.                     *)
(*   5. Resets its idle counter (local activity clock).                    *)
(***************************************************************************)
Step(p) ==
    /\ alive[p]
    /\ LET recvFrom == {q \in Procs : msgs[q][p] # {}}
       IN
       /\ msgs' = [s \in Procs |-> [r \in Procs |->
                     IF r = p THEN {}
                     ELSE IF s = p /\ alive[r] THEN msgs[s][r] \cup {0}
                     ELSE msgs[s][r]]]
       /\ timeout' = [timeout EXCEPT ![p] =
                        [q \in Procs |->
                           IF q \in recvFrom /\ q \in suspected[p]
                              THEN Min(timeout[p][q] + 1, MaxTimeout)
                              ELSE timeout[p][q]]]
       /\ suspected' = [suspected EXCEPT ![p] =
                          {q \in Procs \ {p} :
                              /\ q \notin recvFrom
                              /\ \/ q \in suspected[p]
                                 \/ waiting[p][q] >= timeout[p][q]}]
       /\ waiting' = [waiting EXCEPT ![p] =
                        [q \in Procs |->
                           IF q \in recvFrom THEN 0 ELSE waiting[p][q]]]
       /\ idle' = [idle EXCEPT ![p] = 0]
    /\ UNCHANGED alive

-----------------------------------------------------------------------------
Next ==
    \/ Tick
    \/ \E p \in Procs : Crash(p)
    \/ \E p \in Procs : Step(p)

(***************************************************************************)
(* Fairness conditions:                                                    *)
(*   - Global time keeps advancing (weak fairness on Tick).                *)
(*   - Every live process keeps taking steps (weak fairness on each Step). *)
(*     A crashed process's Step is permanently disabled, so this imposes   *)
(*     nothing on crashed processes.                                       *)
(* No fairness is imposed on Crash.                                        *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(Tick)
    /\ \A p \in Procs : WF_vars(Step(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

\* A process never suspects itself.
NoSelfSuspicion == \A p \in Procs : p \notin suspected[p]

\* At most T processes crash.
CrashBound == Cardinality(Crashed) <= T

\* No message to a live receiver is older than DELTA.
BoundedDelay ==
    \A s, r \in Procs : alive[r] => \A a \in msgs[s][r] : a <= DELTA

\* No live process is idle for more than PHI ticks.
BoundedInactivity == \A p \in Procs : alive[p] => idle[p] <= PHI

\* Crashed processes receive no messages.
NoMsgsToCrashed == \A s, r \in Procs : ~alive[r] => msgs[s][r] = {}

Invariants ==
    /\ TypeOK
    /\ NoSelfSuspicion
    /\ CrashBound
    /\ BoundedDelay
    /\ BoundedInactivity
    /\ NoMsgsToCrashed

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties of the eventually perfect failure detector (<>P).   *)
(* Only finitely many crashes occur. After the last crash, the processes   *)
(* that are alive are exactly the correct processes.                       *)
(***************************************************************************)

\* Strong Completeness: every crashed process is eventually permanently
\* suspected by every correct process.
StrongCompleteness ==
    <>[](\A p, q \in Procs :
            (alive[p] /\ ~alive[q]) => q \in suspected[p])

\* Eventually Strong Accuracy: eventually no correct process is suspected
\* by any correct process.
EventuallyStrongAccuracy ==
    <>[](\A p, q \in Procs :
            (alive[p] /\ alive[q]) => q \notin suspected[p])

THEOREM Spec => []Invariants
THEOREM Spec => StrongCompleteness /\ EventuallyStrongAccuracy
=============================================================================
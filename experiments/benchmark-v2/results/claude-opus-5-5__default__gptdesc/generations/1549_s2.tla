------------------------------- MODULE EPFailureDetectorSystem -------------------------------
(***************************************************************************)
(* A parameterized, partially synchronous distributed system with          *)
(* eventually perfect failure detectors (Chandra and Toueg, "Unreliable    *)
(* Failure Detectors for Reliable Distributed Systems").                   *)
(*                                                                         *)
(* The system composes two parts, inlined here so the module is            *)
(* self-contained:                                                         *)
(*   - Age_Channel: point-to-point channels whose in-transit heartbeat     *)
(*     messages carry an age (the number of global ticks they have been    *)
(*     in transit).                                                        *)
(*   - EPFailureDetector: the behavior of each correct process. It sends   *)
(*     heartbeats, counts ticks since it last heard from each peer,        *)
(*     suspects peers whose silence exceeds an adaptive timeout, and       *)
(*     increases that timeout whenever a suspicion turns out to be false.  *)
(*                                                                         *)
(* Clocks are encoded so that the state space is finite once the           *)
(* parameters are fixed:                                                   *)
(*   - The environment (global) clock is not stored as an unbounded        *)
(*     counter. Each Tick ages every message and advances the local        *)
(*     clocks.                                                             *)
(*   - localClock[p] counts the global ticks since p's last step and is    *)
(*     bounded by PHI.                                                     *)
(*   - heard[p][q] counts the ticks since p last heard from q. It is       *)
(*     saturated at timeout[p][q] + 1.                                     *)
(*   - timeout[p][q] is capped at MaxTimeout.                              *)
(*                                                                         *)
(* Partial synchrony is captured by two constraints:                       *)
(*   - DELTAConstraint: a message to a live receiver is never older than   *)
(*     DELTA, so time cannot pass while such a message has age DELTA.      *)
(*   - PHIConstraint: a live process takes a step at least once every PHI  *)
(*     ticks, so time cannot pass while localClock[p] = PHI.               *)
(*                                                                         *)
(* Model-checking note: TLC handles small instances well (for example      *)
(* N = 2 or 3, T = 1, DELTA = PHI = 1 or 2). The ages in the channels and  *)
(* the PHI-bounded local clocks multiply quickly, so larger DELTA or PHI   *)
(* values cause severe state explosion. Even with these constraints, a     *)
(* StateConstraint is not needed because every variable is bounded by      *)
(* construction.                                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,        \* number of processes
    T,        \* maximum number of crash failures
    DELTA,    \* bound on message delay (in global ticks)
    PHI,      \* bound on relative process speed (ticks between steps)
    d0        \* initial timeout value

ASSUME NAssumption     == N \in Nat \ {0}
ASSUME TAssumption     == T \in Nat /\ T < N
ASSUME DELTAAssumption == DELTA \in Nat \ {0}
ASSUME PHIAssumption   == PHI \in Nat \ {0}
ASSUME d0Assumption    == d0 \in Nat

Procs == 1..N

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

(* A timeout of PHI + DELTA ticks is enough to never falsely suspect a     *)
(* correct process, so timeouts are capped there (or at d0 if larger).     *)
MaxTimeout == Max(d0, PHI + DELTA)

VARIABLES
    crashed,     \* set of crashed processes
    msgs,        \* msgs[s][r] : set of ages of heartbeats in transit s -> r
    localClock,  \* localClock[p] : ticks since p's last step
    heard,       \* heard[p][q] : ticks since p last received from q
    timeout,     \* timeout[p][q] : current timeout p uses for q
    suspected    \* suspected[p] : set of processes p currently suspects

vars == <<crashed, msgs, localClock, heard, timeout, suspected>>

Alive == Procs \ crashed

TypeOK ==
    /\ crashed \subseteq Procs
    /\ msgs \in [Procs -> [Procs -> SUBSET (0..DELTA)]]
    /\ localClock \in [Procs -> 0..PHI]
    /\ timeout \in [Procs -> [Procs -> 0..MaxTimeout]]
    /\ heard \in [Procs -> [Procs -> 0..(MaxTimeout + 1)]]
    /\ suspected \in [Procs -> SUBSET Procs]

-----------------------------------------------------------------------------
(* Partial synchrony constraints                                           *)

(* DELTAConstraint: no message to a live receiver may be older than DELTA. *)
DELTAConstraint ==
    \A s \in Procs, r \in Alive : \A a \in msgs[s][r] : a <= DELTA

(* PHIConstraint: no live process may go more than PHI ticks without a step. *)
PHIConstraint ==
    \A p \in Alive : localClock[p] <= PHI

-----------------------------------------------------------------------------
Init ==
    /\ crashed = {}
    /\ msgs = [s \in Procs |-> [r \in Procs |-> {}]]
    /\ localClock = [p \in Procs |-> 0]
    /\ heard = [p \in Procs |-> [q \in Procs |-> 0]]
    /\ timeout = [p \in Procs |-> [q \in Procs |-> Min(d0, MaxTimeout)]]
    /\ suspected = [p \in Procs |-> {}]

-----------------------------------------------------------------------------
(* Age_Channel and environment actions                                     *)

(* A global clock tick. Every in-transit message ages, the local clocks of *)
(* live processes advance, and the "time since last heard" counters        *)
(* advance (saturating). The tick is only enabled when it would not        *)
(* violate DELTAConstraint or PHIConstraint.                               *)
Tick ==
    /\ \A p \in Alive : localClock[p] < PHI
    /\ \A s \in Procs, r \in Alive : \A a \in msgs[s][r] : a < DELTA
    /\ msgs' = [s \in Procs |-> [r \in Procs |->
                   IF r \in crashed THEN {} ELSE {a + 1 : a \in msgs[s][r]}]]
    /\ localClock' = [p \in Procs |->
                        IF p \in crashed THEN localClock[p]
                        ELSE localClock[p] + 1]
    /\ heard' = [p \in Procs |-> [q \in Procs |->
                    Min(heard[p][q] + 1, timeout[p][q] + 1)]]
    /\ UNCHANGED <<crashed, timeout, suspected>>

(* A process crashes, provided fewer than T processes have crashed. Any    *)
(* messages addressed to it are dropped. Messages it already sent stay in  *)
(* transit.                                                                *)
Crash(p) ==
    /\ p \in Alive
    /\ Cardinality(crashed) < T
    /\ crashed' = crashed \cup {p}
    /\ msgs' = [s \in Procs |-> [r \in Procs |->
                   IF r = p THEN {} ELSE msgs[s][r]]]
    /\ UNCHANGED <<localClock, heard, timeout, suspected>>

-----------------------------------------------------------------------------
(* EPFailureDetector: behavior of a live process                           *)

(* A local step: send a heartbeat to every other live process, suspect     *)
(* every process whose silence has exceeded its timeout, and reset the     *)
(* local clock.                                                            *)
Step(p) ==
    /\ p \in Alive
    /\ msgs' = [s \in Procs |-> [r \in Procs |->
                   IF s = p /\ r # p /\ r \in Alive
                   THEN msgs[s][r] \cup {0}
                   ELSE msgs[s][r]]]
    /\ suspected' = [suspected EXCEPT ![p] =
                        @ \cup {q \in Procs \ {p} : heard[p][q] > timeout[p][q]}]
    /\ localClock' = [localClock EXCEPT ![p] = 0]
    /\ UNCHANGED <<crashed, heard, timeout>>

(* Delivery of a heartbeat of age a from q to p. p stops suspecting q. If  *)
(* that suspicion was false, p increases its timeout for q.                *)
Receive(p, q, a) ==
    /\ p \in Alive
    /\ a \in msgs[q][p]
    /\ msgs' = [msgs EXCEPT ![q][p] = @ \ {a}]
    /\ heard' = [heard EXCEPT ![p][q] = 0]
    /\ IF q \in suspected[p]
          THEN /\ suspected' = [suspected EXCEPT ![p] = @ \ {q}]
               /\ timeout' = [timeout EXCEPT ![p][q] = Min(@ + 1, MaxTimeout)]
          ELSE UNCHANGED <<suspected, timeout>>
    /\ UNCHANGED <<crashed, localClock>>

ReceiveAny(p) == \E q \in Procs, a \in 0..DELTA : Receive(p, q, a)

-----------------------------------------------------------------------------
Next ==
    \/ Tick
    \/ \E p \in Procs : Crash(p)
    \/ \E p \in Procs : Step(p)
    \/ \E p \in Procs : ReceiveAny(p)

Fairness ==
    /\ WF_vars(Tick)
    /\ \A p \in Procs : WF_vars(Step(p))
    /\ \A p \in Procs : WF_vars(ReceiveAny(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants                                                       *)

NoSelfSuspicion == \A p \in Procs : p \notin suspected[p]

SynchronyInv == DELTAConstraint /\ PHIConstraint

-----------------------------------------------------------------------------
(* Liveness properties of an eventually perfect failure detector (<>P)     *)

(* Strong Completeness: every crashed process is eventually permanently    *)
(* suspected by every correct process.                                     *)
StrongCompleteness ==
    \A p, q \in Procs :
        <>[]((q \in crashed /\ p \notin crashed) => q \in suspected[p])

(* Eventually Strong Accuracy: there is a time after which no correct      *)
(* process is suspected by any correct process.                            *)
EventuallyStrongAccuracy ==
    <>[](\A p, q \in Procs :
            (p \notin crashed /\ q \notin crashed) => q \notin suspected[p])

THEOREM Spec => [](TypeOK /\ NoSelfSuspicion /\ SynchronyInv)
THEOREM Spec => StrongCompleteness /\ EventuallyStrongAccuracy
=============================================================================
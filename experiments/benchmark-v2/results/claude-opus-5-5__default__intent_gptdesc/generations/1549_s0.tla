------------------------- MODULE EventuallyPerfectFD -------------------------
(***************************************************************************)
(* Eventually perfect failure detector (<>P) for N processes in a          *)
(* partially synchronous network with up to T permanent crash failures.    *)
(*                                                                         *)
(* Global "environment" ticks advance message ages and enforce:            *)
(*  (1) relative speed: no correct process stays inactive for PHI          *)
(*      consecutive global ticks;                                          *)
(*  (2) message delay: a message to a correct process never ages past      *)
(*      DELTA. Once its age reaches DELTA, the receiver's next receive     *)
(*      step must deliver it.                                              *)
(*                                                                         *)
(* Each process has a bounded local clock that wraps around. The clock     *)
(* value decides the kind of local step:                                   *)
(*    clock = SendPoint     -> send heartbeats (no prediction, no receive) *)
(*    clock = PredictPoint  -> make suspicion decision (no send/receive)   *)
(*    otherwise             -> receive messages                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,              \* number of processes
    T,              \* maximum number of crashes
    DELTA,          \* message-delay bound (in global ticks)
    PHI,            \* relative-speed bound (in global ticks)
    SendPoint,      \* local clock value at which heartbeats are sent
    PredictPoint,   \* local clock value at which suspicions are computed
    ClockMax,       \* local clocks range over 0..ClockMax and wrap around
    MaxAge,         \* bound on the age of messages to crashed processes
    MaxSteps,       \* bound on local steps of a process per global tick
    TOInit,         \* initial timeout estimate
    TOMax           \* maximal timeout estimate (finite domain)

ASSUME /\ N \in Nat \ {0}
       /\ T \in Nat /\ T < N
       /\ DELTA \in Nat /\ DELTA >= 1
       /\ PHI \in Nat /\ PHI >= 1
       /\ ClockMax \in Nat /\ ClockMax >= 2
       /\ SendPoint \in 0..ClockMax
       /\ PredictPoint \in 0..ClockMax
       /\ SendPoint # PredictPoint
       /\ MaxAge \in Nat /\ MaxAge >= DELTA
       /\ MaxSteps \in Nat /\ MaxSteps >= 3
       /\ TOInit \in Nat /\ TOInit >= 1
       /\ TOMax \in Nat /\ TOMax >= TOInit
       \* Timeouts can grow large enough to cover the worst-case
       \* heartbeat gap. Eventual accuracy depends on this.
       /\ TOMax >= MaxSteps * (PHI * (ClockMax + 1) + DELTA + 2)

Proc == 1..N

Min(a, b) == IF a <= b THEN a ELSE b

Msg == [src : Proc, dst : Proc, age : 0..MaxAge]

VARIABLES
    alive,       \* alive[p] = FALSE iff p has crashed (permanent)
    clock,       \* local clock of each process, in 0..ClockMax
    lastHeard,   \* lastHeard[p][q]: local steps of p since p last heard from q
    timeout,     \* timeout[p][q]: p's current timeout estimate for q
    suspected,   \* suspected[p]: set of processes p currently suspects
    msgs,        \* communication channel: set of messages with ages
    steps,       \* steps[p]: local steps p has taken in the current tick
    idle         \* idle[p]: consecutive completed ticks without a step of p

vars == <<alive, clock, lastHeard, timeout, suspected, msgs, steps, idle>>

Crashed == {p \in Proc : ~alive[p]}
Correct == {p \in Proc : alive[p]}

TypeOK ==
    /\ alive \in [Proc -> BOOLEAN]
    /\ clock \in [Proc -> 0..ClockMax]
    /\ lastHeard \in [Proc -> [Proc -> 0..(TOMax + 1)]]
    /\ timeout \in [Proc -> [Proc -> 1..TOMax]]
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ msgs \subseteq Msg
    /\ steps \in [Proc -> 0..MaxSteps]
    /\ idle \in [Proc -> 0..PHI]

Init ==
    /\ alive = [p \in Proc |-> TRUE]
    /\ clock = [p \in Proc |-> 0]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> TOInit]]
    /\ suspected = [p \in Proc |-> {}]
    /\ msgs = {}
    /\ steps = [p \in Proc |-> 0]
    /\ idle = [p \in Proc |-> 0]

(***************************************************************************)
(* Process steps                                                           *)
(***************************************************************************)
NextClock(p) == (clock[p] + 1) % (ClockMax + 1)

\* lastHeard of p after one more local step, saturated at TOMax + 1
AgedLH(p) == [q \in Proc |-> IF q = p THEN 0
                              ELSE Min(lastHeard[p][q] + 1, TOMax + 1)]

Pending(p) == {m \in msgs : m.dst = p}
Urgent(p)  == {m \in Pending(p) : m.age >= DELTA}

StepGuard(p) ==
    /\ alive[p]
    /\ steps[p] < MaxSteps

StepBookkeeping(p) ==
    /\ clock' = [clock EXCEPT ![p] = NextClock(p)]
    /\ steps' = [steps EXCEPT ![p] = steps[p] + 1]

\* Send heartbeats. No prediction and no receipt in this step.
SendStep(p) ==
    /\ StepGuard(p)
    /\ clock[p] = SendPoint
    /\ msgs' = msgs \cup {[src |-> p, dst |-> q, age |-> 0] : q \in Proc \ {p}}
    /\ lastHeard' = [lastHeard EXCEPT ![p] = AgedLH(p)]
    /\ StepBookkeeping(p)
    /\ UNCHANGED <<alive, timeout, suspected, idle>>

\* Make the suspicion decision. No sending and no receipt in this step.
PredictStep(p) ==
    /\ StepGuard(p)
    /\ clock[p] = PredictPoint
    /\ LET lh == AgedLH(p) IN
         /\ lastHeard' = [lastHeard EXCEPT ![p] = lh]
         /\ suspected' = [suspected EXCEPT ![p] =
                             {q \in Proc \ {p} : lh[q] > timeout[p][q]}]
    /\ StepBookkeeping(p)
    /\ UNCHANGED <<alive, timeout, msgs, idle>>

\* Receive a nondeterministic subset of pending messages. Urgent messages
\* (age = DELTA) must be included. If p falsely suspected a sender, p
\* stops suspecting it and increases its timeout for that sender.
ReceiveStep(p) ==
    /\ StepGuard(p)
    /\ clock[p] # SendPoint
    /\ clock[p] # PredictPoint
    /\ \E S \in SUBSET Pending(p) :
         /\ Urgent(p) \subseteq S
         /\ LET senders == {m.src : m \in S}
                lh      == AgedLH(p)
            IN
            /\ msgs' = msgs \ S
            /\ lastHeard' = [lastHeard EXCEPT ![p] =
                               [q \in Proc |-> IF q \in senders THEN 0
                                                ELSE lh[q]]]
            /\ timeout' = [timeout EXCEPT ![p] =
                             [q \in Proc |->
                                IF q \in senders /\ q \in suspected[p]
                                  THEN Min(timeout[p][q] + 1, TOMax)
                                  ELSE timeout[p][q]]]
            /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \ senders]
    /\ StepBookkeeping(p)
    /\ UNCHANGED <<alive, idle>>

Step(p) == SendStep(p) \/ PredictStep(p) \/ ReceiveStep(p)

(***************************************************************************)
(* Crash failures: permanent, at most T of them                           *)
(***************************************************************************)
Crash(p) ==
    /\ alive[p]
    /\ Cardinality(Crashed) < T
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<clock, lastHeard, timeout, suspected, msgs, steps, idle>>

(***************************************************************************)
(* Global environment tick                                                 *)
(***************************************************************************)
\* (1) Relative-speed constraint: a correct process may not stay inactive
\*     for PHI consecutive ticks.
SpeedConstraintOK ==
    \A p \in Proc : alive[p] => (steps[p] > 0 \/ idle[p] + 1 < PHI)

\* (2) Message-delay constraint: a message to a correct process may not
\*     age beyond DELTA.
DelayConstraintOK ==
    ~ \E m \in msgs : alive[m.dst] /\ m.age >= DELTA

Tick ==
    /\ SpeedConstraintOK
    /\ DelayConstraintOK
    \* Age all messages. Messages that reach MaxAge are dropped. By the
    \* delay constraint, only messages to crashed processes can reach it.
    /\ msgs' = { [src |-> m.src, dst |-> m.dst, age |-> m.age + 1] :
                   m \in {x \in msgs : x.age < MaxAge} }
    /\ idle' = [p \in Proc |-> IF steps[p] > 0 THEN 0
                               ELSE Min(idle[p] + 1, PHI)]
    /\ steps' = [p \in Proc |-> 0]
    /\ UNCHANGED <<alive, clock, lastHeard, timeout, suspected>>

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Next ==
    \/ \E p \in Proc : Step(p)
    \/ \E p \in Proc : Crash(p)
    \/ Tick

Fairness ==
    /\ \A p \in Proc : WF_vars(Step(p))
    /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
CrashBound == Cardinality(Crashed) <= T

\* No message to a correct process ever exceeds age DELTA.
ChannelDelayBound ==
    \A m \in msgs : alive[m.dst] => m.age <= DELTA

\* Every message has bounded age.
ChannelAgeBound == \A m \in msgs : m.age <= MaxAge

\* No correct process exceeds PHI idle ticks.
SpeedBound == \A p \in Proc : alive[p] => idle[p] < PHI

\* A process never suspects itself.
NoSelfSuspicion == \A p \in Proc : p \notin suspected[p]

\* Sending and predicting never happen in the same local step.
SendPredictDisjoint == SendPoint # PredictPoint

Invariants ==
    /\ TypeOK
    /\ CrashBound
    /\ ChannelDelayBound
    /\ ChannelAgeBound
    /\ SpeedBound
    /\ NoSelfSuspicion
    /\ SendPredictDisjoint

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* Strong completeness: every crashed process is eventually permanently
\* suspected by every correct process.
StrongCompleteness ==
    \A p, q \in Proc :
        <>[]( (~alive[q] /\ alive[p]) => q \in suspected[p] )

\* Eventual strong accuracy: there is a time after which no correct
\* process is suspected by any correct process.
EventualStrongAccuracy ==
    <>[]( \A p, q \in Proc :
            (alive[p] /\ alive[q]) => q \notin suspected[p] )

\* Crashes are permanent.
CrashPermanent ==
    \A p \in Proc : [](~alive[p] => [](~alive[p]))

THEOREM Spec => []Invariants
THEOREM Spec => StrongCompleteness /\ EventualStrongAccuracy
=============================================================================
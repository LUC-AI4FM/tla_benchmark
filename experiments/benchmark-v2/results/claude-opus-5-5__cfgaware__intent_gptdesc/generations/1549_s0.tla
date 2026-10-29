------------------------------ MODULE EventuallyPerfectFD ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,              \* number of processes
    T,              \* maximal number of crashes
    d0,             \* initial timeout estimate (message-delay bound guess)
    SendPoint,      \* local clock value at which heartbeats are sent
    PredictPoint,   \* local clock value at which suspicions are computed
    DELTA,          \* message-delay bound (in global ticks)
    PHI             \* relative-speed bound (in global ticks)

ASSUME N \in Nat /\ N >= 1
ASSUME T \in Nat /\ T < N
ASSUME d0 \in Nat
ASSUME DELTA \in Nat
ASSUME PHI \in Nat /\ PHI >= 1
ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # PredictPoint

Proc == 1..N

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

\* Local clocks wrap with this period.
ClockPeriod == Max(SendPoint, PredictPoint) + 1

\* Maximal age of a message (receivers step at least once every PHI ticks,
\* and must accept messages of age >= DELTA when they step).
MaxAge == DELTA + PHI

\* Upper bound on timeout estimates; large enough to exceed the real
\* worst-case gap between heartbeat receptions from a correct process.
MaxTimeout == Max(d0, ClockPeriod * PHI + DELTA + 2 * PHI + 2)

\* Cap of the "steps since last heard" counter (strictly above any timeout).
MaxHeard == MaxTimeout + 1

VARIABLES
    alive,       \* alive[i] : process i has not crashed
    clock,       \* clock[i] : local clock of i, in 0..ClockPeriod-1
    lastHeard,   \* lastHeard[i][j] : local steps of i since last heartbeat from j
    timeout,     \* timeout[i][j] : i's current timeout estimate for j
    suspected,   \* suspected[i][j] : i currently suspects j
    buf,         \* buf[s][r] : age of oldest pending heartbeat s->r, or -1
    idle,        \* idle[i] : global ticks since i's last step
    stepped      \* stepped[i] : i already stepped in the current tick

vars == <<alive, clock, lastHeard, timeout, suspected, buf, idle, stepped>>

TypeOK ==
    /\ alive \in [Proc -> BOOLEAN]
    /\ clock \in [Proc -> 0..(ClockPeriod - 1)]
    /\ lastHeard \in [Proc -> [Proc -> 0..MaxHeard]]
    /\ timeout \in [Proc -> [Proc -> 0..MaxTimeout]]
    /\ suspected \in [Proc -> [Proc -> BOOLEAN]]
    /\ buf \in [Proc -> [Proc -> (-1)..MaxAge]]
    /\ idle \in [Proc -> 0..PHI]
    /\ stepped \in [Proc -> BOOLEAN]

Init ==
    /\ alive = [i \in Proc |-> TRUE]
    /\ clock = [i \in Proc |-> 0]
    /\ lastHeard = [i \in Proc |-> [j \in Proc |-> 0]]
    /\ timeout = [i \in Proc |-> [j \in Proc |-> d0]]
    /\ suspected = [i \in Proc |-> [j \in Proc |-> FALSE]]
    /\ buf = [s \in Proc |-> [r \in Proc |-> -1]]
    /\ idle = [i \in Proc |-> 0]
    /\ stepped = [i \in Proc |-> FALSE]

Pending(i)   == {j \in Proc : buf[j][i] >= 0}
Mandatory(i) == {j \in Pending(i) : buf[j][i] >= DELTA}

(***************************************************************************)
(* A local step of process i. It receives a nondeterministic subset of the *)
(* pending heartbeats (at least all those of age >= DELTA), then, depending *)
(* on its local clock, either sends heartbeats (SendPoint), or predicts    *)
(* (PredictPoint), or does neither. Since SendPoint # PredictPoint, sending *)
(* and predicting never happen in the same step.                           *)
(***************************************************************************)
Step(i) ==
    /\ alive[i]
    /\ ~stepped[i]
    /\ \E R \in SUBSET Pending(i) :
        /\ Mandatory(i) \subseteq R
        /\ LET c == clock[i]
               hb(j) == IF j \in R THEN 0
                        ELSE Min(lastHeard[i][j] + 1, MaxHeard)
               to1(j) == IF j \in R /\ suspected[i][j]
                         THEN Min(timeout[i][j] + 1, MaxTimeout)
                         ELSE timeout[i][j]
               susp1(j) == IF j \in R THEN FALSE ELSE suspected[i][j]
           IN
           /\ lastHeard' = [lastHeard EXCEPT ![i] =
                              [j \in Proc |-> IF j = i THEN 0 ELSE hb(j)]]
           /\ timeout' = [timeout EXCEPT ![i] = [j \in Proc |-> to1(j)]]
           /\ suspected' = [suspected EXCEPT ![i] =
                              [j \in Proc |->
                                 IF j = i THEN FALSE
                                 ELSE IF c = PredictPoint THEN hb(j) > to1(j)
                                 ELSE susp1(j)]]
           /\ buf' = [s \in Proc |-> [r \in Proc |->
                        IF r = i /\ s \in R THEN -1
                        ELSE IF s = i /\ r # i /\ c = SendPoint /\ buf[s][r] = -1
                             THEN 0
                        ELSE buf[s][r]]]
           /\ clock' = [clock EXCEPT ![i] = (c + 1) % ClockPeriod]
    /\ idle' = [idle EXCEPT ![i] = 0]
    /\ stepped' = [stepped EXCEPT ![i] = TRUE]
    /\ UNCHANGED alive

(***************************************************************************)
(* Global environment tick: ages all messages and advances inactivity      *)
(* counters. Disabled if some correct process has been inactive for PHI    *)
(* ticks (relative-speed constraint).                                      *)
(***************************************************************************)
Tick ==
    /\ \A i \in Proc : alive[i] => idle[i] < PHI
    /\ buf' = [s \in Proc |-> [r \in Proc |->
                 IF buf[s][r] = -1 THEN -1
                 ELSE IF ~alive[r] /\ buf[s][r] >= MaxAge THEN -1
                 ELSE Min(buf[s][r] + 1, MaxAge)]]
    /\ idle' = [i \in Proc |-> IF alive[i] THEN Min(idle[i] + 1, PHI) ELSE idle[i]]
    /\ stepped' = [i \in Proc |-> FALSE]
    /\ UNCHANGED <<alive, clock, lastHeard, timeout, suspected>>

Crash(i) ==
    /\ alive[i]
    /\ Cardinality({j \in Proc : ~alive[j]}) < T
    /\ alive' = [alive EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<clock, lastHeard, timeout, suspected, buf, idle, stepped>>

Next ==
    \/ Tick
    \/ \E i \in Proc : Step(i)
    \/ \E i \in Proc : Crash(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Tick)
    /\ \A i \in Proc : WF_vars(Step(i))

-----------------------------------------------------------------------------

StrongCompleteness ==
    \A i, j \in Proc :
        (i # j) => <>[]((alive[i] /\ ~alive[j]) => suspected[i][j])

EventuallyStrongAccuracy ==
    <>[](\A i, j \in Proc : (alive[i] /\ alive[j]) => ~suspected[i][j])

NeverPermanentlySuspected ==
    \A i, j \in Proc :
        (i # j) => ([]<>(~suspected[i][j]) \/ <>(~alive[i]) \/ <>(~alive[j]))

StateConstraint ==
    \A i, j \in Proc :
        /\ timeout[i][j] <= MaxTimeout
        /\ lastHeard[i][j] <= MaxHeard

=============================================================================
---------------------------- MODULE HourlyHeartbeat ----------------------------
EXTENDS Reals

CONSTANTS
    Hour,              \* nominal heartbeat period (e.g. 60 or 3600)
    Tolerance,         \* half-width of the tolerance window around Hour
    ClockMin,          \* lower bound of the real-valued clock domain
    HeartbeatCond(_, _) \* abstract heartbeat condition from an external module

ASSUME HourAssump      == Hour \in Real /\ Hour > 0
ASSUME TolAssump       == Tolerance \in Real /\ 0 <= Tolerance /\ Tolerance < Hour
ASSUME ClockMinAssump  == ClockMin \in Real

VARIABLES
    now,        \* global continuous-time clock
    timer,      \* local timer, reset by each heartbeat
    hbEnabled   \* heartbeat control signal (may toggle nondeterministically)

vars == <<now, timer, hbEnabled>>

\* Clock domain: reals bounded below by ClockMin
ClockDomain == {r \in Real : r >= ClockMin}

\* Timer bounds relative to the hourly target, accounting for tolerance
TimerMin == 0
TimerMax == Hour + Tolerance

\* Tolerance window in which the heartbeat may occur
InWindow(t) == /\ Hour - Tolerance <= t
               /\ t <= Hour + Tolerance

-----------------------------------------------------------------------------
TypeOK ==
    /\ now \in ClockDomain
    /\ timer \in Real
    /\ hbEnabled \in BOOLEAN

Init ==
    /\ now \in ClockDomain
    /\ timer = 0
    /\ hbEnabled = TRUE

\* Time advances by an arbitrary positive real amount; timer follows the clock
\* but may never exceed its maximum bound.
Tick ==
    \E d \in Real :
        /\ d > 0
        /\ timer + d <= TimerMax
        /\ now' = now + d
        /\ timer' = timer + d
        /\ UNCHANGED hbEnabled

\* Heartbeat: only permitted inside the tolerance window; resets the timer.
Heartbeat ==
    /\ hbEnabled
    /\ InWindow(timer)
    /\ timer' = 0
    /\ UNCHANGED <<now, hbEnabled>>

\* Nondeterministic toggling of the heartbeat control signal.
Toggle ==
    /\ hbEnabled' = ~hbEnabled
    /\ UNCHANGED <<now, timer>>

Next == Tick \/ Heartbeat \/ Toggle

\* Clock progress beyond a fixed bound b
TickPast(b) == Tick /\ now' > b

\* Non-Zeno condition: the clock eventually exceeds any finite real threshold
NZ == \A r \in Real : <>(now > r)

Fairness ==
    /\ SF_vars(Heartbeat)
    /\ WF_vars(Tick)
    /\ \A b \in Real : WF_vars(TickPast(b))

Spec == Init /\ [][Next]_vars /\ Fairness /\ NZ

-----------------------------------------------------------------------------
\* Safety invariants
TimerBounds == TimerMin <= timer /\ timer <= TimerMax

ClockInDomain == now \in ClockDomain

Invariants == TypeOK /\ TimerBounds /\ ClockInDomain

\* Clock monotonicity: time never reverses
ClockMonotone == [][now' >= now]_vars

\* Timer either resets on heartbeat or advances exactly as the clock does
TimerTracksClock ==
    [][ \/ timer' = 0
        \/ timer' - timer = now' - now ]_vars

\* Heartbeat resets only occur within the tolerance window
ResetOnlyInWindow ==
    [][ (timer' = 0 /\ timer # 0) => InWindow(timer) ]_vars

-----------------------------------------------------------------------------
\* Liveness properties
InvariantsAlways == []Invariants

\* The abstract external heartbeat condition eventually (and repeatedly) holds
HeartbeatCondEventually == []<>HeartbeatCond(now, timer)

\* Heartbeats happen infinitely often
HeartbeatRecurs == []<>(timer = 0)

\* Clock is unbounded (no Zeno behaviors)
ClockUnbounded == \A r \in Real : <>(now > r)

\* No state permanently avoids clock values that are repeatedly enabled
NoPermanentAvoidance ==
    \A r \in Real :
        ([]<>(ENABLED (Tick /\ now' >= r))) => <>(now >= r)

THEOREM Spec => []Invariants
THEOREM Spec => ClockMonotone /\ TimerTracksClock /\ ResetOnlyInWindow
THEOREM Spec => HeartbeatRecurs /\ ClockUnbounded /\ NoPermanentAvoidance
=============================================================================
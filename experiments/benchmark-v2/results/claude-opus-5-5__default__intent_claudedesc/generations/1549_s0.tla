---------------------------- MODULE EventuallyPerfectFD ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,              \* number of processes
    T,              \* maximum number of crashes
    SendPoint,      \* period (in local clock ticks) of heartbeat broadcasts
    PredictPoint,   \* period (in local clock ticks) of suspicion updates
    PHI,            \* relative-speed bound
    DELTA,          \* message-delay bound
    InitDelta       \* initial per-peer timeout

ASSUME /\ N \in Nat \ {0}
       /\ T \in 0..N
       /\ SendPoint \in Nat \ {0}
       /\ PredictPoint \in Nat \ {0}
       /\ PHI \in Nat \ {0}
       /\ DELTA \in Nat \ {0}
       /\ InitDelta \in Nat

Proc == 1..N

ClockMod == SendPoint * PredictPoint

Min(a, b) == IF a < b THEN a ELSE b

VARIABLES
    alive,          \* set of non-crashed processes
    localClock,     \* localClock[p] : local clock of p (modular)
    delta,          \* delta[p][q] : timeout of p for peer q
    suspected,      \* suspected[p] : suspicion set of p
    fromLastHeard,  \* fromLastHeard[p][q] : steps of p since it last heard from q
    inTransit,      \* set of in-transit messages [src, dst, age]
    moved,          \* processes that already acted in the current global tick
    procPause       \* procPause[p] : global ticks since p last acted

vars == << alive, localClock, delta, suspected, fromLastHeard,
           inTransit, moved, procPause >>

Msg == [src : Proc, dst : Proc, age : 0..DELTA]

TypeOK ==
    /\ alive \subseteq Proc
    /\ localClock \in [Proc -> 0..(ClockMod - 1)]
    /\ delta \in [Proc -> [Proc -> Nat]]
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ fromLastHeard \in [Proc -> [Proc -> Nat]]
    /\ inTransit \subseteq Msg
    /\ moved \subseteq Proc
    /\ procPause \in [Proc -> Nat]

CrashBound == Cardinality(Proc \ alive) <= T

PHIRespected == \A p \in alive : procPause[p] < PHI

-----------------------------------------------------------------------------
Init ==
    /\ alive = Proc
    /\ localClock = [p \in Proc |-> 0]
    /\ delta = [p \in Proc |-> [q \in Proc |-> InitDelta]]
    /\ suspected = [p \in Proc |-> {}]
    /\ fromLastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ inTransit = {}
    /\ moved = {}
    /\ procPause = [p \in Proc |-> 0]

\* Counter increment applied on every step of p, kept finite
IncHeard(p) ==
    [q \in Proc |-> Min(fromLastHeard[p][q] + 1, delta[p][q] + 1)]

IsSendTick(p)    == localClock[p] % SendPoint = 0
IsPredictTick(p) == ~IsSendTick(p) /\ localClock[p] % PredictPoint = 0
IsReceiveTick(p) == ~IsSendTick(p) /\ ~IsPredictTick(p)

\* Broadcast "alive" heartbeats
SendAlive(p) ==
    /\ IsSendTick(p)
    /\ inTransit' = inTransit \cup
                    { [src |-> p, dst |-> q, age |-> 0] : q \in Proc \ {p} }
    /\ fromLastHeard' = [fromLastHeard EXCEPT ![p] = IncHeard(p)]
    /\ UNCHANGED << delta, suspected >>

\* Update the suspicion set
Predict(p) ==
    /\ IsPredictTick(p)
    /\ suspected' = [suspected EXCEPT ![p] =
                        suspected[p] \cup
                        { q \in Proc \ {p} : fromLastHeard[p][q] > delta[p][q] }]
    /\ fromLastHeard' = [fromLastHeard EXCEPT ![p] = IncHeard(p)]
    /\ UNCHANGED << delta, inTransit >>

\* Receive messages; every message of age >= DELTA addressed to p must be delivered
Receive(p) ==
    /\ IsReceiveTick(p)
    /\ LET ToP == { m \in inTransit : m.dst = p }
       IN \E D \in SUBSET ToP :
            /\ { m \in ToP : m.age >= DELTA } \subseteq D
            /\ LET heard == { m.src : m \in D }
                   inc   == IncHeard(p)
               IN /\ inTransit' = inTransit \ D
                  /\ fromLastHeard' = [fromLastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF q \in heard THEN 0 ELSE inc[q]]]
                  /\ delta' = [delta EXCEPT ![p] =
                        [q \in Proc |-> IF q \in heard \cap suspected[p]
                                          THEN delta[p][q] + 1
                                          ELSE delta[p][q]]]
                  /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \ heard]

\* A correct process acts at most once per global tick, doing exactly one operation
Step(p) ==
    /\ p \in alive
    /\ p \notin moved
    /\ \/ SendAlive(p)
       \/ Predict(p)
       \/ Receive(p)
    /\ localClock' = [localClock EXCEPT ![p] = (localClock[p] + 1) % ClockMod]
    /\ moved' = moved \cup {p}
    /\ UNCHANGED << alive, procPause >>

\* Permanent crash of a process
Crash(p) ==
    /\ p \in alive
    /\ Cardinality(Proc \ alive) < T
    /\ alive' = alive \ {p}
    /\ UNCHANGED << localClock, delta, suspected, fromLastHeard,
                    inTransit, moved, procPause >>

\* Flush messages involving crashed processes
Flush ==
    \E m \in inTransit :
        /\ \/ m.src \notin alive
           \/ m.dst \notin alive
        /\ inTransit' = inTransit \ {m}
        /\ UNCHANGED << alive, localClock, delta, suspected, fromLastHeard,
                        moved, procPause >>

\* Global environmental tick: at least one correct process acted, and the
\* relative-speed bound PHI is not violated.
Tick ==
    /\ moved \cap alive # {}
    /\ \A p \in alive \ moved : procPause[p] + 1 < PHI
    /\ inTransit' = { [src |-> m.src, dst |-> m.dst,
                       age |-> Min(m.age + 1, DELTA)] : m \in inTransit }
    /\ procPause' = [p \in Proc |-> IF p \in moved THEN 0 ELSE procPause[p] + 1]
    /\ moved' = {}
    /\ UNCHANGED << alive, localClock, delta, suspected, fromLastHeard >>

Next ==
    \/ \E p \in Proc : Step(p)
    \/ \E p \in Proc : Crash(p)
    \/ Flush
    \/ Tick

Fairness ==
    /\ WF_vars(Tick)
    /\ WF_vars(Flush)
    /\ \A p \in Proc : WF_vars(Step(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety invariants
Invariants == TypeOK /\ CrashBound /\ PHIRespected

\* Strong Completeness: every crashed process is eventually and permanently
\* suspected by every correct process.
StrongCompleteness ==
    \A p, q \in Proc :
        <>[]((p \in alive /\ q \notin alive) => q \in suspected[p])

\* Eventually Strong Accuracy: eventually no correct process is suspected
\* by any correct process.
EventuallyStrongAccuracy ==
    <>[](\A p, q \in Proc :
            (p \in alive /\ q \in alive) => q \notin suspected[p])

THEOREM Spec => []Invariants
THEOREM Spec => StrongCompleteness /\ EventuallyStrongAccuracy
=============================================================================
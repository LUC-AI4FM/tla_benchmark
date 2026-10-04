-------------------------------- MODULE FastMutex --------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES
    pc,           \* Program counter for each process
    intent,       \* Per-process intent flags (boolean)
    tour1,        \* First coordination register (process id or 0)
    tour2,        \* Second coordination register (process id or 0)
    waitingOn     \* For spinning: which process (if any) we're waiting on

vars == <<pc, intent, tour1, tour2, waitingOn>>

\* Program counter states
\* "idle"       - not trying to enter CS
\* "setIntent"  - about to set intent flag
\* "writeTour1" - about to write to tour1
\* "readTour2a" - first read of tour2 (fast path check)
\* "writeTour2" - about to write to tour2
\* "readTour1"  - read tour1 to check if we won fast path
\* "checkFast"  - evaluate fast path condition
\* "resetIntent"- reset intent for slow path spin
\* "spinFlags"  - spinning on other processes' intent flags
\* "checkTour2" - check if tour2 still equals self
\* "cs"         - in critical section
\* "exit"       - exiting critical section
\* "backoff"    - backing off to retry

TypeOK ==
    /\ pc \in [Procs -> {"idle", "setIntent", "writeTour1", "readTour2a", 
                         "writeTour2", "readTour1", "checkFast", "resetIntent",
                         "spinFlags", "checkTour2", "cs", "exit", "backoff"}]
    /\ intent \in [Procs -> BOOLEAN]
    /\ tour1 \in Procs \cup {0}
    /\ tour2 \in Procs \cup {0}
    /\ waitingOn \in [Procs -> Procs \cup {0}]

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ intent = [p \in Procs |-> FALSE]
    /\ tour1 = 0
    /\ tour2 = 0
    /\ waitingOn = [p \in Procs |-> 0]

\* Process p starts trying to enter CS
StartEntry(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "setIntent"]
    /\ UNCHANGED <<intent, tour1, tour2, waitingOn>>

\* Set intent flag
SetIntent(p) ==
    /\ pc[p] = "setIntent"
    /\ intent' = [intent EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "writeTour1"]
    /\ UNCHANGED <<tour1, tour2, waitingOn>>

\* Write self to tour1
WriteTour1(p) ==
    /\ pc[p] = "writeTour1"
    /\ tour1' = p
    /\ pc' = [pc EXCEPT ![p] = "readTour2a"]
    /\ UNCHANGED <<intent, tour2, waitingOn>>

\* Fast path: check if tour2 is free
ReadTour2a(p) ==
    /\ pc[p] = "readTour2a"
    /\ IF tour2 = 0
       THEN pc' = [pc EXCEPT ![p] = "writeTour2"]
       ELSE pc' = [pc EXCEPT ![p] = "resetIntent"]  \* Someone else is ahead, go slow path
    /\ UNCHANGED <<intent, tour1, tour2, waitingOn>>

\* Write self to tour2
WriteTour2(p) ==
    /\ pc[p] = "writeTour2"
    /\ tour2' = p
    /\ pc' = [pc EXCEPT ![p] = "readTour1"]
    /\ UNCHANGED <<intent, tour1, waitingOn>>

\* Read tour1 to see if we won the race
ReadTour1(p) ==
    /\ pc[p] = "readTour1"
    /\ pc' = [pc EXCEPT ![p] = "checkFast"]
    /\ UNCHANGED <<intent, tour1, tour2, waitingOn>>

\* Check fast path condition
CheckFast(p) ==
    /\ pc[p] = "checkFast"
    /\ IF tour1 = p
       THEN pc' = [pc EXCEPT ![p] = "cs"]  \* Won fast path
       ELSE pc' = [pc EXCEPT ![p] = "resetIntent"]  \* Lost, go slow path
    /\ UNCHANGED <<intent, tour1, tour2, waitingOn>>

\* Reset intent for slow path (to avoid deadlock while spinning)
ResetIntent(p) ==
    /\ pc[p] = "resetIntent"
    /\ intent' = [intent EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "spinFlags"]
    /\ waitingOn' = [waitingOn EXCEPT ![p] = 1]  \* Start checking from process 1
    /\ UNCHANGED <<tour1, tour2>>

\* Spin waiting for other processes' intent flags to be false
\* This models checking each process's flag in turn
SpinFlags(p) ==
    /\ pc[p] = "spinFlags"
    /\ LET w == waitingOn[p]
       IN IF w > N
          THEN \* Done checking all processes
               /\ pc' = [pc EXCEPT ![p] = "checkTour2"]
               /\ waitingOn' = [waitingOn EXCEPT ![p] = 0]
          ELSE IF w = p
               THEN \* Skip self
                    /\ waitingOn' = [waitingOn EXCEPT ![p] = w + 1]
                    /\ pc' = pc
               ELSE IF ~intent[w]
                    THEN \* This process's intent is false, move to next
                         /\ waitingOn' = [waitingOn EXCEPT ![p] = w + 1]
                         /\ pc' = pc
                    ELSE \* Keep waiting on this process (spin)
                         /\ pc' = pc
                         /\ waitingOn' = waitingOn
    /\ UNCHANGED <<intent, tour1, tour2>>

\* After spinning, check if tour2 still points to us
CheckTour2(p) ==
    /\ pc[p] = "checkTour2"
    /\ IF tour2 = p
       THEN \* We can enter CS via slow path
            /\ intent' = [intent EXCEPT ![p] = TRUE]  \* Re-assert intent
            /\ pc' = [pc EXCEPT ![p] = "cs"]
       ELSE \* Lost our slot, back off and retry
            /\ pc' = [pc EXCEPT ![p] = "backoff"]
            /\ intent' = intent
    /\ UNCHANGED <<tour1, tour2, waitingOn>>

\* Back off: reset and retry the whole protocol
Backoff(p) ==
    /\ pc[p] = "backoff"
    /\ pc' = [pc EXCEPT ![p] = "setIntent"]
    /\ UNCHANGED <<intent, tour1, tour2, waitingOn>>

\* Critical section - process is in CS
\* This is just a marker state, actual work would happen here
InCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<intent, tour1, tour2, waitingOn>>

\* Exit critical section and cleanup
Exit(p) ==
    /\ pc[p] = "exit"
    /\ intent' = [intent EXCEPT ![p] = FALSE]
    /\ tour2' = 0  \* Clear tour2 to allow others
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<tour1, waitingOn>>

\* Combined action for process p
Process(p) ==
    \/ StartEntry(p)
    \/ SetIntent(p)
    \/ WriteTour1(p)
    \/ ReadTour2a(p)
    \/ WriteTour2(p)
    \/ ReadTour1(p)
    \/ CheckFast(p)
    \/ ResetIntent(p)
    \/ SpinFlags(p)
    \/ CheckTour2(p)
    \/ Backoff(p)
    \/ InCS(p)
    \/ Exit(p)

Next == \E p \in Procs : Process(p)

\* Weak fairness for each process's actions
Fairness == \A p \in Procs : WF_vars(Process(p))

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* SAFETY PROPERTIES
--------------------------------------------------------------------------------

\* Mutual Exclusion: At most one process in critical section
MutualExclusion ==
    \A p1, p2 \in Procs : 
        (pc[p1] = "cs" /\ pc[p2] = "cs") => p1 = p2

\* Alternative formulation
AtMostOneInCS ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

\* Safety invariant combining type correctness and mutual exclusion
SafetyInvariant == TypeOK /\ MutualExclusion

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES
--------------------------------------------------------------------------------

\* System-wide progress: infinitely often some process enters CS
\* (if processes keep trying)
SystemProgress ==
    []<>(\E p \in Procs : pc[p] = "cs")

\* Starvation freedom: every process that starts trying eventually enters CS
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "setIntent") ~> (pc[p] = "cs")

\* Weaker property: if a process wants to enter, it eventually does
EventualEntry ==
    \A p \in Procs : [](pc[p] # "idle" => <>(pc[p] = "cs"))

\* Every process that enters CS eventually exits
EventualExit ==
    \A p \in Procs : [](pc[p] = "cs" => <>(pc[p] = "idle"))

--------------------------------------------------------------------------------
\* AUXILIARY PROPERTIES FOR DEBUGGING
--------------------------------------------------------------------------------

\* At least one process is not idle (for checking interesting behaviors)
SomeActivity == \E p \in Procs : pc[p] # "idle"

\* No deadlock: if some process is trying, someone can make progress
NoDeadlock ==
    (\E p \in Procs : pc[p] # "idle" /\ pc[p] # "cs") =>
    (\E p \in Procs : ENABLED(Process(p)))

================================================================================
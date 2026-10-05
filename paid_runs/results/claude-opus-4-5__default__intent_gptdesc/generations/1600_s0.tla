---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANT N

ASSUME N > 1

CONSTANTS IDLE, INTENT, FAST_TRY, CHECK_OWNER, SLOW_PATH, WAIT_OTHERS, CRITICAL, EXIT

ProcessSet == 1..N

NONE == 0

VARIABLES
    pc,           \* Program counter for each process
    flag,         \* Intent flag for each process (TRUE = interested)
    owner,        \* Shared owner indicator (0 = none, 1..N = process id)
    turn,         \* Used in slow path for contention resolution
    waiting,      \* Set of processes in slow path waiting
    inCS          \* Set of processes currently in critical section

vars == <<pc, flag, owner, turn, waiting, inCS>>

TypeOK ==
    /\ pc \in [ProcessSet -> {IDLE, INTENT, FAST_TRY, CHECK_OWNER, SLOW_PATH, WAIT_OTHERS, CRITICAL, EXIT}]
    /\ flag \in [ProcessSet -> BOOLEAN]
    /\ owner \in 0..N
    /\ turn \in 0..N
    /\ waiting \subseteq ProcessSet
    /\ inCS \subseteq ProcessSet

Init ==
    /\ pc = [p \in ProcessSet |-> IDLE]
    /\ flag = [p \in ProcessSet |-> FALSE]
    /\ owner = NONE
    /\ turn = NONE
    /\ waiting = {}
    /\ inCS = {}

\* Process p expresses intent to enter critical section
ExpressIntent(p) ==
    /\ pc[p] = IDLE
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = INTENT]
    /\ UNCHANGED <<owner, turn, waiting, inCS>>

\* Process p attempts fast acquisition
TryFastPath(p) ==
    /\ pc[p] = INTENT
    /\ IF owner = NONE
       THEN /\ owner' = p
            /\ pc' = [pc EXCEPT ![p] = FAST_TRY]
       ELSE /\ pc' = [pc EXCEPT ![p] = SLOW_PATH]
            /\ UNCHANGED owner
    /\ UNCHANGED <<flag, turn, waiting, inCS>>

\* Check if fast path succeeded (no other process grabbed ownership)
CheckFastSuccess(p) ==
    /\ pc[p] = FAST_TRY
    /\ IF owner = p
       THEN \* Check if any other process has intent
            IF \E q \in ProcessSet \ {p} : flag[q]
            THEN \* Contention detected, back off to slow path
                 /\ owner' = NONE
                 /\ pc' = [pc EXCEPT ![p] = SLOW_PATH]
                 /\ UNCHANGED <<flag, turn, waiting, inCS>>
            ELSE \* Fast path success - enter critical section
                 /\ pc' = [pc EXCEPT ![p] = CRITICAL]
                 /\ inCS' = inCS \union {p}
                 /\ UNCHANGED <<flag, owner, turn, waiting>>
       ELSE \* Lost ownership race, go to slow path
            /\ pc' = [pc EXCEPT ![p] = SLOW_PATH]
            /\ UNCHANGED <<flag, owner, turn, waiting, inCS>>

\* Process enters slow path - set turn and join waiting set
EnterSlowPath(p) ==
    /\ pc[p] = SLOW_PATH
    /\ turn' = p
    /\ waiting' = waiting \union {p}
    /\ pc' = [pc EXCEPT ![p] = WAIT_OTHERS]
    /\ UNCHANGED <<flag, owner, inCS>>

\* In slow path, wait for others to clear or for turn
WaitForWindow(p) ==
    /\ pc[p] = WAIT_OTHERS
    /\ \/ \* All other flagged processes have lower priority or cleared
          /\ \A q \in ProcessSet \ {p} : 
               (~flag[q] \/ (q \in waiting /\ turn # q))
          /\ owner = NONE
          /\ owner' = p
          /\ waiting' = waiting \ {p}
          /\ pc' = [pc EXCEPT ![p] = CRITICAL]
          /\ inCS' = inCS \union {p}
          /\ UNCHANGED <<flag, turn>>
       \/ \* Back off and retry - non-deterministic choice to avoid livelock
          /\ \E q \in ProcessSet \ {p} : flag[q] /\ q \notin waiting
          /\ waiting' = waiting \ {p}
          /\ flag' = [flag EXCEPT ![p] = FALSE]
          /\ pc' = [pc EXCEPT ![p] = IDLE]
          /\ UNCHANGED <<owner, turn, inCS>>

\* Exit critical section - proper cleanup
ExitCS(p) ==
    /\ pc[p] = CRITICAL
    /\ pc' = [pc EXCEPT ![p] = EXIT]
    /\ inCS' = inCS \ {p}
    /\ UNCHANGED <<flag, owner, turn, waiting>>

\* Complete exit - clear all ownership and intent markers
CompleteExit(p) ==
    /\ pc[p] = EXIT
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ owner' = IF owner = p THEN NONE ELSE owner
    /\ pc' = [pc EXCEPT ![p] = IDLE]
    /\ UNCHANGED <<turn, waiting, inCS>>

\* Combined Next action for process p
ProcessAction(p) ==
    \/ ExpressIntent(p)
    \/ TryFastPath(p)
    \/ CheckFastSuccess(p)
    \/ EnterSlowPath(p)
    \/ WaitForWindow(p)
    \/ ExitCS(p)
    \/ CompleteExit(p)

Next == \E p \in ProcessSet : ProcessAction(p)

\* Fairness: weak fairness for all process actions
\* This ensures no process is permanently ignored
Fairness == \A p \in ProcessSet : WF_vars(ProcessAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ===========================================================================
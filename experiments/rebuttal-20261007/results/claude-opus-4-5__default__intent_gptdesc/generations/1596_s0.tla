-------------------------------- MODULE FastMutex --------------------------------
\* Fast mutual exclusion protocol for N asynchronous processes
\* Based on Lamport's Fast Mutex algorithm structure

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N  \* Number of processes

ASSUME N \in Nat /\ N > 0

Procs == 1..N

\* Process states in the protocol
\* idle: not attempting to enter CS
\* start: beginning entry protocol, announcing intent
\* fast: attempting fast path (writing to X)
\* check: checking if won fast path
\* wait: entering slow path, setting flag
\* spin: spinning/waiting for conditions
\* critical: in critical section
\* exit: leaving critical section

VARIABLES
    pc,         \* pc[p] = program counter/state of process p
    flag,       \* flag[p] = TRUE if process p has announced intent
    X,          \* First coordination variable: last process to try fast path
    Y,          \* Second coordination variable: winner of slow path (0 = none)
    inCS        \* Set of processes currently in critical section (for invariant)

vars == <<pc, flag, X, Y, inCS>>

TypeOK ==
    /\ pc \in [Procs -> {"idle", "start", "fast", "check", "wait", "spin", "critical", "exit"}]
    /\ flag \in [Procs -> BOOLEAN]
    /\ X \in Procs \cup {0}
    /\ Y \in Procs \cup {0}
    /\ inCS \subseteq Procs

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ flag = [p \in Procs |-> FALSE]
    /\ X = 0
    /\ Y = 0
    /\ inCS = {}

\* Process p starts entry protocol by announcing intent
Start(p) ==
    /\ pc[p] = "idle"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "start"]
    /\ UNCHANGED <<X, Y, inCS>>

\* Process p attempts fast path by writing to X
TryFast(p) ==
    /\ pc[p] = "start"
    /\ X' = p
    /\ pc' = [pc EXCEPT ![p] = "fast"]
    /\ UNCHANGED <<flag, Y, inCS>>

\* Process p checks if Y is free (part of fast path check)
CheckY(p) ==
    /\ pc[p] = "fast"
    /\ IF Y = 0
       THEN pc' = [pc EXCEPT ![p] = "check"]
       ELSE pc' = [pc EXCEPT ![p] = "wait"]  \* Contention, go to slow path
    /\ UNCHANGED <<flag, X, Y, inCS>>

\* Process p verifies it still owns X (fast path verification)
VerifyFast(p) ==
    /\ pc[p] = "check"
    /\ IF X = p
       THEN \* Won fast path, enter critical section
            /\ pc' = [pc EXCEPT ![p] = "critical"]
            /\ inCS' = inCS \cup {p}
            /\ UNCHANGED <<flag, X, Y>>
       ELSE \* Lost fast path, go to slow path
            /\ pc' = [pc EXCEPT ![p] = "wait"]
            /\ UNCHANGED <<flag, X, Y, inCS>>

\* Process p enters slow path by claiming Y
EnterSlow(p) ==
    /\ pc[p] = "wait"
    /\ Y = 0
    /\ Y' = p
    /\ pc' = [pc EXCEPT ![p] = "spin"]
    /\ UNCHANGED <<flag, X, inCS>>

\* Process p spins waiting for X holder to clear or detects it can proceed
\* Checks that no other process has a higher priority claim via X
SpinWait(p) ==
    /\ pc[p] = "spin"
    /\ Y = p  \* We still own Y
    /\ \A q \in Procs \ {p} : 
        \/ ~flag[q]  \* Others have cleared their flags
        \/ X = p     \* Or we own X
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ inCS' = inCS \cup {p}
    /\ UNCHANGED <<flag, X, Y>>

\* Process p aborts slow path attempt due to contention (Y taken by another)
AbortSlow(p) ==
    /\ pc[p] = "wait"
    /\ Y /= 0
    /\ Y /= p
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<X, Y, inCS>>

\* Process p aborts from spin state (lost Y or timeout)
AbortSpin(p) ==
    /\ pc[p] = "spin"
    /\ Y /= p  \* Lost ownership of Y
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<X, Y, inCS>>

\* Process p executes critical section (stays or moves to exit)
\* This is a placeholder for arbitrary CS work
InCritical(p) ==
    /\ pc[p] = "critical"
    /\ p \in inCS
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<flag, X, Y, inCS>>

\* Process p exits critical section and releases locks
Exit(p) ==
    /\ pc[p] = "exit"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ Y' = IF Y = p THEN 0 ELSE Y  \* Release Y if we held it
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ inCS' = inCS \ {p}
    /\ UNCHANGED <<X>>

\* Individual process actions
ProcAction(p) ==
    \/ Start(p)
    \/ TryFast(p)
    \/ CheckY(p)
    \/ VerifyFast(p)
    \/ EnterSlow(p)
    \/ SpinWait(p)
    \/ AbortSlow(p)
    \/ AbortSpin(p)
    \/ InCritical(p)
    \/ Exit(p)

Next == \E p \in Procs : ProcAction(p)

\* Fairness: weak fairness for each process's actions
Fairness == \A p \in Procs : WF_vars(ProcAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* SAFETY PROPERTIES

\* Mutual exclusion: at most one process in critical section
MutualExclusion == Cardinality(inCS) <= 1

\* Alternative formulation using pc
MutualExclusionPC == \A p, q \in Procs : 
    (pc[p] = "critical" /\ pc[q] = "critical") => p = q

\* Type correctness is also a safety property
Safety == TypeOK /\ MutualExclusion

--------------------------------------------------------------------------------
\* LIVENESS PROPERTIES

\* Someone is trying to enter (announced intent or further along)
SomeoneTrying == \E p \in Procs : pc[p] /= "idle"

\* Someone is in the critical section
SomeoneInCS == \E p \in Procs : pc[p] = "critical"

\* Global progress: if processes keep trying, eventually someone enters
GlobalProgress == SomeoneTrying ~> SomeoneInCS

\* No permanent starvation: every process that starts eventually enters
NoStarvation == \A p \in Procs : 
    (pc[p] = "start") ~> (pc[p] = "critical")

\* Infinitely often someone enters the critical section
InfiniteProgress == []<>SomeoneInCS

\* Every process that wants to enter eventually does (under fairness)
EventualEntry == \A p \in Procs :
    [](pc[p] = "start" => <>(pc[p] = "critical"))

--------------------------------------------------------------------------------
\* INVARIANTS for model checking

\* If a process is in CS, it should be in inCS set
ConsistentCS == \A p \in Procs :
    pc[p] = "critical" <=> p \in inCS

\* Y holder is in appropriate state
YHolderConsistent == 
    Y /= 0 => (pc[Y] \in {"spin", "critical", "exit"} \/ flag[Y])

\* Process in critical section has its flag set (until exit completes)
FlagInCS == \A p \in Procs :
    pc[p] = "critical" => flag[p]

================================================================================
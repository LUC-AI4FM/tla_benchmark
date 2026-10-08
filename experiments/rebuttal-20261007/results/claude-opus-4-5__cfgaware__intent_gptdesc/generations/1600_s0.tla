---------------------------- MODULE MutualExclusion ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N, defaultInitValue

ASSUME N > 1

VARIABLES
    pc,           \* Program counter for each process
    flag,         \* flag[i] = TRUE means process i has expressed intent
    owner,        \* owner = i means process i owns the lock, 0 means no owner
    contention,   \* contention[i] = TRUE means process i detected contention
    waiting       \* waiting[i] = TRUE means process i is in slow path waiting

vars == <<pc, flag, owner, contention, waiting>>

Procs == 1..N

States == {"idle", "intent", "fast_try", "fast_success", "contention_detected", 
           "slow_wait", "slow_check", "slow_try", "cs", "exit", "cleanup"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ flag \in [Procs -> BOOLEAN]
    /\ owner \in 0..N
    /\ contention \in [Procs -> BOOLEAN]
    /\ waiting \in [Procs -> BOOLEAN]

Init ==
    /\ pc = [i \in Procs |-> "idle"]
    /\ flag = [i \in Procs |-> FALSE]
    /\ owner = 0
    /\ contention = [i \in Procs |-> FALSE]
    /\ waiting = [i \in Procs |-> FALSE]

\* Process expresses intent to enter critical section
ExpressIntent(i) ==
    /\ pc[i] = "idle"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "intent"]
    /\ UNCHANGED <<owner, contention, waiting>>

\* Process attempts fast path acquisition
FastTry(i) ==
    /\ pc[i] = "intent"
    /\ pc' = [pc EXCEPT ![i] = "fast_try"]
    /\ UNCHANGED <<flag, owner, contention, waiting>>

\* Fast path succeeds - no other process has flag set and no owner
FastSuccess(i) ==
    /\ pc[i] = "fast_try"
    /\ owner = 0
    /\ \A j \in Procs \ {i} : ~flag[j]
    /\ owner' = i
    /\ pc' = [pc EXCEPT ![i] = "fast_success"]
    /\ UNCHANGED <<flag, contention, waiting>>

\* Fast path detects contention - another process has flag or there's an owner
DetectContention(i) ==
    /\ pc[i] = "fast_try"
    /\ \/ owner /= 0
       \/ \E j \in Procs \ {i} : flag[j]
    /\ contention' = [contention EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "contention_detected"]
    /\ UNCHANGED <<flag, owner, waiting>>

\* After fast success, enter critical section
EnterFromFast(i) ==
    /\ pc[i] = "fast_success"
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<flag, owner, contention, waiting>>

\* Withdraw intent and start slow path waiting
WithdrawAndWait(i) ==
    /\ pc[i] = "contention_detected"
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ waiting' = [waiting EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "slow_wait"]
    /\ UNCHANGED <<owner, contention>>

\* In slow path, wait until owner releases
SlowWait(i) ==
    /\ pc[i] = "slow_wait"
    /\ owner = 0
    /\ pc' = [pc EXCEPT ![i] = "slow_check"]
    /\ UNCHANGED <<flag, owner, contention, waiting>>

\* Check if other processes are not actively trying
SlowCheck(i) ==
    /\ pc[i] = "slow_check"
    /\ \A j \in Procs \ {i} : ~(flag[j] /\ ~waiting[j])
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ waiting' = [waiting EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "slow_try"]
    /\ UNCHANGED <<owner, contention>>

\* Slow check fails - back to waiting
SlowCheckFail(i) ==
    /\ pc[i] = "slow_check"
    /\ \E j \in Procs \ {i} : flag[j] /\ ~waiting[j]
    /\ pc' = [pc EXCEPT ![i] = "slow_wait"]
    /\ UNCHANGED <<flag, owner, contention, waiting>>

\* Slow path try succeeds
SlowTrySuccess(i) ==
    /\ pc[i] = "slow_try"
    /\ owner = 0
    /\ owner' = i
    /\ contention' = [contention EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<flag, waiting>>

\* Slow path try fails - go back to contention detected
SlowTryFail(i) ==
    /\ pc[i] = "slow_try"
    /\ owner /= 0
    /\ pc' = [pc EXCEPT ![i] = "contention_detected"]
    /\ UNCHANGED <<flag, owner, contention, waiting>>

\* Exit critical section
ExitCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<flag, owner, contention, waiting>>

\* Cleanup - clear flag and release ownership
Cleanup(i) ==
    /\ pc[i] = "exit"
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ owner' = 0
    /\ contention' = [contention EXCEPT ![i] = FALSE]
    /\ waiting' = [waiting EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "idle"]

\* All actions for a process
Process(i) ==
    \/ ExpressIntent(i)
    \/ FastTry(i)
    \/ FastSuccess(i)
    \/ DetectContention(i)
    \/ EnterFromFast(i)
    \/ WithdrawAndWait(i)
    \/ SlowWait(i)
    \/ SlowCheck(i)
    \/ SlowCheckFail(i)
    \/ SlowTrySuccess(i)
    \/ SlowTryFail(i)
    \/ ExitCS(i)
    \/ Cleanup(i)

Next == \E i \in Procs : Process(i)

\* Fairness: Each process gets fair scheduling
Fairness == \A i \in Procs : WF_vars(Process(i))

\* The complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* ----- SAFETY PROPERTIES -----

\* Mutual exclusion: at most one process in critical section
MutualExclusion ==
    \A i, j \in Procs : (pc[i] = "cs" /\ pc[j] = "cs") => i = j

\* Alternative formulation
AtMostOneInCS == Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

\* Owner consistency: if someone is in CS, they must be the owner
OwnerConsistency ==
    \A i \in Procs : pc[i] = "cs" => owner = i

\* If there's an owner, they should be in CS or exiting
OwnerInCS == owner /= 0 => \E i \in Procs : (owner = i /\ pc[i] \in {"cs", "exit", "fast_success"})

\* Proper cleanup verification: after cleanup, process has released everything
CleanupComplete ==
    \A i \in Procs : pc[i] = "idle" => 
        /\ ~flag[i]
        /\ ~contention[i]
        /\ ~waiting[i]
        /\ owner /= i

\* Combined invariant for safety
Invariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ OwnerConsistency

\* ----- LIVENESS PROPERTIES -----

\* Global progress: eventually some process enters critical section
GlobalProgress == <>(\E i \in Procs : pc[i] = "cs")

\* From any state, eventually someone enters CS (always can make progress)
AlwaysProgress == []<>(\E i \in Procs : pc[i] = "cs")

\* No deadlock: system can always make some transition or some process is in CS
NoDeadlock == 
    \/ \E i \in Procs : pc[i] = "cs"
    \/ ENABLED Next

\* Starvation freedom (each interested process eventually gets in)
\* If a process expresses intent, it eventually enters CS
NoStarvation == \A i \in Procs : (pc[i] = "intent") ~> (pc[i] = "cs")

\* Progress under contention: if contention detected, eventually either CS or retry
ContentionProgress == 
    \A i \in Procs : (pc[i] = "contention_detected") ~> (pc[i] \in {"cs", "idle"})

\* Combined liveness property
Liveness == 
    /\ AlwaysProgress
    /\ NoStarvation
    /\ ContentionProgress

================================================================================
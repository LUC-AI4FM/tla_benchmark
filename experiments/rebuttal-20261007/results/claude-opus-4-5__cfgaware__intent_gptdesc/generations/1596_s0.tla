---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N, M

ASSUME N \in Nat /\ N > 0
ASSUME M \in Nat /\ M > 0

Procs == 1..N

VARIABLES
    pc,           \* Program counter for each process
    flag,         \* flag[i] \in {"idle", "want", "wait", "crit"} - announcement state
    gate1,        \* First coordination variable (holds process id or 0)
    gate2,        \* Second coordination variable (holds process id or 0)
    waitCount     \* waitCount[i] - bounded counter for waiting/retry logic

vars == <<pc, flag, gate1, gate2, waitCount>>

\* Program counter states:
\* "start"    - beginning of entry protocol
\* "announce" - announced intent, about to write gate1
\* "check1"   - wrote gate1, checking gate2
\* "setgate2" - setting gate2 to self
\* "check2"   - checking if gate1 still equals self
\* "wait"     - waiting for others to leave
\* "spin"     - spinning on flags
\* "cs"       - in critical section
\* "exit"     - leaving critical section
\* "abort"    - detected contention, aborting

TypeOK ==
    /\ pc \in [Procs -> {"start", "announce", "check1", "setgate2", 
                         "check2", "wait", "spin", "cs", "exit", "abort"}]
    /\ flag \in [Procs -> {"idle", "want", "wait", "crit"}]
    /\ gate1 \in (Procs \cup {0})
    /\ gate2 \in (Procs \cup {0})
    /\ waitCount \in [Procs -> 0..M]

Init ==
    /\ pc = [i \in Procs |-> "start"]
    /\ flag = [i \in Procs |-> "idle"]
    /\ gate1 = 0
    /\ gate2 = 0
    /\ waitCount = [i \in Procs |-> 0]

\* Process i starts entry protocol by announcing intent
Start(i) ==
    /\ pc[i] = "start"
    /\ flag' = [flag EXCEPT ![i] = "want"]
    /\ pc' = [pc EXCEPT ![i] = "announce"]
    /\ UNCHANGED <<gate1, gate2, waitCount>>

\* Process i writes itself to gate1
Announce(i) ==
    /\ pc[i] = "announce"
    /\ gate1' = i
    /\ pc' = [pc EXCEPT ![i] = "check1"]
    /\ UNCHANGED <<flag, gate2, waitCount>>

\* Process i checks gate2; if zero, proceed fast path; otherwise slow path
Check1(i) ==
    /\ pc[i] = "check1"
    /\ IF gate2 = 0
       THEN pc' = [pc EXCEPT ![i] = "setgate2"]
       ELSE pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED <<flag, gate1, gate2, waitCount>>

\* Process i sets gate2 to itself (fast path)
SetGate2(i) ==
    /\ pc[i] = "setgate2"
    /\ gate2' = i
    /\ pc' = [pc EXCEPT ![i] = "check2"]
    /\ UNCHANGED <<flag, gate1, waitCount>>

\* Process i checks if gate1 still equals self
Check2(i) ==
    /\ pc[i] = "check2"
    /\ IF gate1 = i
       THEN pc' = [pc EXCEPT ![i] = "cs"]  \* Fast path success
       ELSE /\ pc' = [pc EXCEPT ![i] = "spin"]
            /\ flag' = [flag EXCEPT ![i] = "wait"]
    /\ UNCHANGED <<gate1, gate2, waitCount>>

\* Process i waits/spins, checking other processes' flags
\* Can either continue waiting or detect contention and abort
Wait(i) ==
    /\ pc[i] = "wait"
    /\ \/ /\ \A j \in Procs \ {i} : flag[j] \in {"idle", "want"}
          /\ pc' = [pc EXCEPT ![i] = "setgate2"]
          /\ UNCHANGED waitCount
       \/ /\ waitCount[i] < M
          /\ waitCount' = [waitCount EXCEPT ![i] = @ + 1]
          /\ pc' = [pc EXCEPT ![i] = "wait"]
       \/ /\ waitCount[i] >= M
          /\ pc' = [pc EXCEPT ![i] = "abort"]
          /\ UNCHANGED waitCount
    /\ UNCHANGED <<flag, gate1, gate2>>

\* Process i spins waiting for gate2 to be self or for opportunity
Spin(i) ==
    /\ pc[i] = "spin"
    /\ \/ /\ gate2 = i
          /\ \A j \in Procs \ {i} : flag[j] # "crit"
          /\ pc' = [pc EXCEPT ![i] = "cs"]
          /\ UNCHANGED waitCount
       \/ /\ gate2 # i
          /\ pc' = [pc EXCEPT ![i] = "abort"]
          /\ UNCHANGED waitCount
       \/ /\ waitCount[i] < M
          /\ waitCount' = [waitCount EXCEPT ![i] = @ + 1]
          /\ pc' = [pc EXCEPT ![i] = "spin"]
    /\ UNCHANGED <<flag, gate1, gate2>>

\* Process i enters critical section
EnterCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ flag' = [flag EXCEPT ![i] = "crit"]
    /\ UNCHANGED <<gate1, gate2, waitCount>>

\* Process i exits critical section
Exit(i) ==
    /\ pc[i] = "exit"
    /\ flag' = [flag EXCEPT ![i] = "idle"]
    /\ gate2' = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ waitCount' = [waitCount EXCEPT ![i] = 0]
    /\ UNCHANGED gate1

\* Process i aborts due to contention, resets state and retries
Abort(i) ==
    /\ pc[i] = "abort"
    /\ flag' = [flag EXCEPT ![i] = "idle"]
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ waitCount' = [waitCount EXCEPT ![i] = 0]
    /\ UNCHANGED <<gate1, gate2>>

\* Combined action for process i
Process(i) ==
    \/ Start(i)
    \/ Announce(i)
    \/ Check1(i)
    \/ SetGate2(i)
    \/ Check2(i)
    \/ Wait(i)
    \/ Spin(i)
    \/ EnterCS(i)
    \/ Exit(i)
    \/ Abort(i)

Next == \E i \in Procs : Process(i)

\* Fairness: weak fairness for each process's actions
Fairness == \A i \in Procs : WF_vars(Process(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual Exclusion - at most one process in critical section
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(flag[i] = "crit" /\ flag[j] = "crit")

\* Alternative formulation: cardinality of processes with crit flag <= 1
MutualExclusionAlt ==
    Cardinality({i \in Procs : flag[i] = "crit"}) <= 1

\* The main invariant combines type correctness and mutual exclusion
Invariant == TypeOK /\ MutualExclusion

\* Liveness: Eventually some process enters the critical section
\* Global progress: infinitely often some process is in CS
GlobalProgress == []<>(\E i \in Procs : flag[i] = "crit")

\* No starvation: if a process starts trying, it eventually enters CS
NoStarvation == \A i \in Procs : [](pc[i] = "announce" => <>(flag[i] = "crit"))

\* Combined liveness property
Liveness == GlobalProgress /\ NoStarvation

==========================================================================
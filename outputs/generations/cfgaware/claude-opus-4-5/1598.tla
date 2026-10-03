---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, S, pc

vars == <<x, y, b, S, pc>>

Procs == 1..N

Labels == {"start", "l1", "l2", "l3", "l4", "l5", "l6", "l7", "cs", "l8", "l9", "done"}

TypeOK ==
    /\ x \in (Procs \cup {0})
    /\ y \in (Procs \cup {0})
    /\ b \in [Procs -> BOOLEAN]
    /\ S \in [Procs -> SUBSET Procs]
    /\ pc \in [Procs -> Labels]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ S = [i \in Procs |-> {}]
    /\ pc = [i \in Procs |-> "start"]

\* Process i starts competing for critical section
start(i) ==
    /\ pc[i] = "start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "l1"]
    /\ UNCHANGED <<y, S>>

\* Check if y is 0
l1(i) ==
    /\ pc[i] = "l1"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![i] = FALSE]
            /\ pc' = [pc EXCEPT ![i] = "l2"]
       ELSE /\ pc' = [pc EXCEPT ![i] = "l3"]
            /\ UNCHANGED b
    /\ UNCHANGED <<x, y, S>>

\* Wait until y = 0, then restart
l2(i) ==
    /\ pc[i] = "l2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

\* Set y to i
l3(i) ==
    /\ pc[i] = "l3"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "l4"]
    /\ UNCHANGED <<x, b, S>>

\* Check if x = i (fast path)
l4(i) ==
    /\ pc[i] = "l4"
    /\ IF x /= i
       THEN /\ b' = [b EXCEPT ![i] = FALSE]
            /\ pc' = [pc EXCEPT ![i] = "l5"]
       ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
            /\ UNCHANGED b
    /\ UNCHANGED <<x, y, S>>

\* Collect all processes with b[j] = TRUE into S[i]
l5(i) ==
    /\ pc[i] = "l5"
    /\ S' = [S EXCEPT ![i] = {j \in Procs : b[j]}]
    /\ pc' = [pc EXCEPT ![i] = "l6"]
    /\ UNCHANGED <<x, y, b>>

\* Check if y = i (slow path validation)
l6(i) ==
    /\ pc[i] = "l6"
    /\ IF y /= i
       THEN /\ pc' = [pc EXCEPT ![i] = "l2"]
       ELSE /\ pc' = [pc EXCEPT ![i] = "l7"]
    /\ UNCHANGED <<x, y, b, S>>

\* Wait until all processes in S[i] have b[j] = FALSE
l7(i) ==
    /\ pc[i] = "l7"
    /\ \A j \in S[i] : ~b[j]
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b, S>>

\* Critical section
cs(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "l8"]
    /\ UNCHANGED <<x, y, b, S>>

\* Exit critical section: reset y
l8(i) ==
    /\ pc[i] = "l8"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![i] = "l9"]
    /\ UNCHANGED <<x, b, S>>

\* Reset b[i]
l9(i) ==
    /\ pc[i] = "l9"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<x, y, S>>

\* Process can restart from done
done(i) ==
    /\ pc[i] = "done"
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

\* Action for process i
proc(i) ==
    \/ start(i)
    \/ l1(i)
    \/ l2(i)
    \/ l3(i)
    \/ l4(i)
    \/ l5(i)
    \/ l6(i)
    \/ l7(i)
    \/ cs(i)
    \/ l8(i)
    \/ l9(i)
    \/ done(i)

Next == \E i \in Procs : proc(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Mutual exclusion: at most one process in critical section
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Invariant == MutualExclusion

\* Liveness: infinitely often some process is in the critical section
Liveness == []<>(\E i \in Procs : pc[i] = "cs")

==========================================================================
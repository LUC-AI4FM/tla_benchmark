---------------- MODULE FastMutex ----------------

EXTENDS Integers, FiniteSets, TLC

CONSTANT N
ASSUME N \in Nat \ {0}

Procs == 1..N

VARIABLES x, y, b, S, pc

vars == <<x, y, b, S, pc>>

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ S = [i \in Procs |-> {}]
    /\ pc = [i \in Procs |-> "NonCritical"]

NonCritical(i) ==
    /\ pc[i] = "NonCritical"
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<x, y, b, S>>

Start(i) ==
    /\ pc[i] = "Start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "L2"]
    /\ UNCHANGED <<y, S>>

L2(i) ==
    /\ pc[i] = "L2"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![i] = FALSE]
            /\ pc' = [pc EXCEPT ![i] = "L5"]
            /\ UNCHANGED <<x, y, S>>
       ELSE /\ y' = i
            /\ pc' = [pc EXCEPT ![i] = "L3"]
            /\ UNCHANGED <<x, b, S>>

L3(i) ==
    /\ pc[i] = "L3"
    /\ IF x = i
       THEN /\ pc' = [pc EXCEPT ![i] = "CS"]
            /\ UNCHANGED <<x, y, b, S>>
       ELSE /\ b' = [b EXCEPT ![i] = FALSE]
            /\ S' = [S EXCEPT ![i] = {j \in Procs : b[j]}]
            /\ pc' = [pc EXCEPT ![i] = "L4"]
            /\ UNCHANGED <<x, y>>

L4(i) ==
    /\ pc[i] = "L4"
    /\ \A j \in S[i] : ~b[j]
    /\ pc' = [pc EXCEPT ![i] = "L3a"]
    /\ UNCHANGED <<x, y, b, S>>

L3a(i) ==
    /\ pc[i] = "L3a"
    /\ IF y /= i
       THEN /\ pc' = [pc EXCEPT ![i] = "L5"]
            /\ UNCHANGED <<x, y, b, S>>
       ELSE /\ pc' = [pc EXCEPT ![i] = "CS"]
            /\ UNCHANGED <<x, y, b, S>>

L5(i) ==
    /\ pc[i] = "L5"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<x, y, b, S>>

CS(i) ==
    /\ pc[i] = "CS"
    /\ y' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ S' = [S EXCEPT ![i] = {}]
    /\ pc' = [pc EXCEPT ![i] = "NonCritical"]
    /\ UNCHANGED <<x>>

Next == \E i \in Procs :
            \/ NonCritical(i)
            \/ Start(i)
            \/ L2(i)
            \/ L3(i)
            \/ L4(i)
            \/ L3a(i)
            \/ L5(i)
            \/ CS(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

Invariant == MutualExclusion

Liveness == []<>(\E i \in Procs : pc[i] = "CS")

=============================================================================
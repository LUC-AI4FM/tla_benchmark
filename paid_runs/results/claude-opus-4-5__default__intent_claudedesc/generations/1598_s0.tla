---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLES x, y, b, pc

Procs == 1..N

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "setb", "setx", "sety", "checky", "checkx", 
                         "waitloop", "cs", "clearb", "cleary", "clearbfinal"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]

\* Non-critical section - process decides to enter
ncs(i) ==
    /\ pc[i] = "ncs"
    /\ pc' = [pc EXCEPT ![i] = "setb"]
    /\ UNCHANGED <<x, y, b>>

\* Set own flag to true
setb(i) ==
    /\ pc[i] = "setb"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "setx"]
    /\ UNCHANGED <<x, y>>

\* Write identity to x
setx(i) ==
    /\ pc[i] = "setx"
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "sety"]
    /\ UNCHANGED <<y, b>>

\* Write identity to y
sety(i) ==
    /\ pc[i] = "sety"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "checky"]
    /\ UNCHANGED <<x, b>>

\* Check if y still equals self (first contention check)
checky(i) ==
    /\ pc[i] = "checky"
    /\ IF y = i
       THEN pc' = [pc EXCEPT ![i] = "checkx"]
       ELSE pc' = [pc EXCEPT ![i] = "clearb"]
    /\ UNCHANGED <<x, y, b>>

\* Check if x still equals self (second contention check)
checkx(i) ==
    /\ pc[i] = "checkx"
    /\ IF x = i
       THEN pc' = [pc EXCEPT ![i] = "cs"]
       ELSE pc' = [pc EXCEPT ![i] = "waitloop"]
    /\ UNCHANGED <<x, y, b>>

\* Back off: clear flag and wait for y to become 0
clearb(i) ==
    /\ pc[i] = "clearb"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "waitloop"]
    /\ UNCHANGED <<x, y>>

\* Wait until y is clear, then retry
waitloop(i) ==
    /\ pc[i] = "waitloop"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "setb"]
    /\ UNCHANGED <<x, y, b>>

\* Critical section - process is in CS
cs(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "cleary"]
    /\ UNCHANGED <<x, y, b>>

\* Clear y when exiting CS
cleary(i) ==
    /\ pc[i] = "cleary"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![i] = "clearbfinal"]
    /\ UNCHANGED <<x, b>>

\* Clear own flag when exiting CS
clearbfinal(i) ==
    /\ pc[i] = "clearbfinal"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, y>>

\* Process i takes a step
Step(i) ==
    \/ ncs(i)
    \/ setb(i)
    \/ setx(i)
    \/ sety(i)
    \/ checky(i)
    \/ checkx(i)
    \/ clearb(i)
    \/ waitloop(i)
    \/ cs(i)
    \/ cleary(i)
    \/ clearbfinal(i)

Next == \E i \in Procs : Step(i)

\* Weak fairness over all process steps
Fairness == \A i \in Procs : WF_<<x, y, b, pc>>(Step(i))

Spec == Init /\ [][Next]_<<x, y, b, pc>> /\ Fairness

\* Safety: Mutual Exclusion - no two distinct processes in CS
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: Some process enters CS infinitely often
SomeoneEntersCS == \E i \in Procs : pc[i] = "cs"
LivenessProperty == []<>SomeoneEntersCS

==========================================================================
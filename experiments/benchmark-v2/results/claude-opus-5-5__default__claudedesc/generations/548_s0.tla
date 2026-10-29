---------------------------- MODULE PetersonN ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs  == 0 .. (N - 1)
Levels == 0 .. (N - 2)

VARIABLES
    level,          \* level[p] \in -1..N-2 : current contention level of p
    last_to_enter,  \* last_to_enter[l] : process that most recently arrived at level l
    pc,             \* program counter of each process
    l               \* local loop counter (level being attempted) of each process

vars == << level, last_to_enter, pc, l >>

PCs == {"ncs", "set_level", "set_last", "wait", "cs", "exit"}

TypeOK ==
    /\ level \in [Procs -> -1 .. (N - 2)]
    /\ last_to_enter \in [Levels -> Procs]
    /\ pc \in [Procs -> PCs]
    /\ l \in [Procs -> 0 .. (N - 1)]

Init ==
    /\ level = [p \in Procs |-> -1]
    /\ last_to_enter = [i \in Levels |-> 0]
    /\ pc = [p \in Procs |-> "ncs"]
    /\ l = [p \in Procs |-> 0]

\* Leave the non-critical section and start the entry protocol
NonCritical(p) ==
    /\ pc[p] = "ncs"
    /\ l' = [l EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "set_level"]
    /\ UNCHANGED << level, last_to_enter >>

\* Loop head: either announce presence at level l[p], or enter the CS
SetLevel(p) ==
    /\ pc[p] = "set_level"
    /\ IF l[p] < N - 1
          THEN /\ level' = [level EXCEPT ![p] = l[p]]
               /\ pc' = [pc EXCEPT ![p] = "set_last"]
          ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
               /\ UNCHANGED level
    /\ UNCHANGED << last_to_enter, l >>

\* Mark self as the last to enter the current level
SetLast(p) ==
    /\ pc[p] = "set_last"
    /\ last_to_enter' = [last_to_enter EXCEPT ![l[p]] = p]
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED << level, l >>

\* Wait while p is the last to enter and some other process is at the
\* same or a higher level; proceed otherwise.
Wait(p) ==
    /\ pc[p] = "wait"
    /\ \/ last_to_enter[l[p]] # p
       \/ \A k \in Procs \ {p} : level[k] < l[p]
    /\ l' = [l EXCEPT ![p] = l[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "set_level"]
    /\ UNCHANGED << level, last_to_enter >>

\* Critical section
Critical(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED << level, last_to_enter, l >>

\* Exit protocol
Exit(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = -1]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED << last_to_enter, l >>

Proc(p) ==
    \/ NonCritical(p)
    \/ SetLevel(p)
    \/ SetLast(p)
    \/ Wait(p)
    \/ Critical(p)
    \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Spec == Init /\ [][Next]_vars

\* Not asserted by the module; provided for checking the intended property.
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

=============================================================================
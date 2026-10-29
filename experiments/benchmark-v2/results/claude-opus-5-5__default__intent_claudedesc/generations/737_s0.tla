------------------------------ MODULE Bakery ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N,        \* number of processes
          MaxNat    \* upper bound on ticket numbers (for bounded model checking)

ASSUME NAssump   == N \in Nat \ {0}
ASSUME MaxAssump == MaxNat \in Nat \ {0}

Procs == 1..N

\* Lexicographic ordering on <<ticket, pid>> pairs: lower ticket wins,
\* ties broken by lower process identifier.
a \prec b == \/ a[1] < b[1]
             \/ /\ a[1] = b[1]
                /\ a[2] < b[2]

VARIABLES num,        \* num[i]       : ticket number of process i (0 = no ticket)
          flag,       \* flag[i]      : TRUE while process i is choosing its ticket
          unchecked,  \* unchecked[i] : processes i still has to examine
          mx,         \* mx[i]        : largest ticket seen so far while choosing
          nxt,        \* nxt[i]       : process currently being waited on
          pc          \* pc[i]        : control location of process i

vars == <<num, flag, unchecked, mx, nxt, pc>>

Labels   == {"ncs", "e1", "e2", "e3", "w1", "w2", "cs", "exit"}
Trying   == {"e1", "e2", "e3", "w1", "w2"}

TypeOK ==
    /\ num       \in [Procs -> 0..MaxNat]
    /\ flag      \in [Procs -> BOOLEAN]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ mx        \in [Procs -> 0..MaxNat]
    /\ nxt       \in [Procs -> Procs]
    /\ pc        \in [Procs -> Labels]

Init ==
    /\ num       = [i \in Procs |-> 0]
    /\ flag      = [i \in Procs |-> FALSE]
    /\ unchecked = [i \in Procs |-> {}]
    /\ mx        = [i \in Procs |-> 0]
    /\ nxt       = [i \in Procs |-> 1]
    /\ pc        = [i \in Procs |-> "ncs"]

---------------------------------------------------------------------------
\* Non-critical section: process decides to request the critical section.
ncs(i) ==
    /\ pc[i] = "ncs"
    /\ flag'      = [flag EXCEPT ![i] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
    /\ mx'        = [mx EXCEPT ![i] = 0]
    /\ pc'        = [pc EXCEPT ![i] = "e1"]
    /\ UNCHANGED <<num, nxt>>

\* Doorway: read the other processes' tickets one at a time to find the max.
e1(i) ==
    /\ pc[i] = "e1"
    /\ IF unchecked[i] # {}
         THEN \E j \in unchecked[i] :
                /\ unchecked' = [unchecked EXCEPT ![i] = @ \ {j}]
                /\ mx' = [mx EXCEPT ![i] = IF num[j] > @ THEN num[j] ELSE @]
                /\ UNCHANGED pc
         ELSE /\ pc' = [pc EXCEPT ![i] = "e2"]
              /\ UNCHANGED <<unchecked, mx>>
    /\ UNCHANGED <<num, flag, nxt>>

\* Take a ticket one larger than any seen (bounded by MaxNat).
e2(i) ==
    /\ pc[i] = "e2"
    /\ mx[i] + 1 <= MaxNat
    /\ num' = [num EXCEPT ![i] = mx[i] + 1]
    /\ pc'  = [pc EXCEPT ![i] = "e3"]
    /\ UNCHANGED <<flag, unchecked, mx, nxt>>

\* Finish choosing; prepare to wait on every other process.
e3(i) ==
    /\ pc[i] = "e3"
    /\ flag'      = [flag EXCEPT ![i] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
    /\ pc'        = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<num, mx, nxt>>

\* Wait until some unchecked process j is not choosing; or enter CS if done.
w1(i) ==
    /\ pc[i] = "w1"
    /\ IF unchecked[i] # {}
         THEN \E j \in unchecked[i] :
                /\ ~flag[j]
                /\ nxt' = [nxt EXCEPT ![i] = j]
                /\ pc'  = [pc EXCEPT ![i] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
              /\ UNCHANGED nxt
    /\ UNCHANGED <<num, flag, unchecked, mx>>

\* Wait until j has no ticket or i has priority over j.
w2(i) ==
    /\ pc[i] = "w2"
    /\ LET j == nxt[i] IN
         /\ \/ num[j] = 0
            \/ <<num[i], i>> \prec <<num[j], j>>
         /\ unchecked' = [unchecked EXCEPT ![i] = @ \ {j}]
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<num, flag, mx, nxt>>

\* Critical section.
cs(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<num, flag, unchecked, mx, nxt>>

\* Exit: release ticket.
exit(i) ==
    /\ pc[i] = "exit"
    /\ num' = [num EXCEPT ![i] = 0]
    /\ pc'  = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<flag, unchecked, mx, nxt>>

\* All steps except leaving the non-critical section (which need not happen).
NonNcs(i) == e1(i) \/ e2(i) \/ e3(i) \/ w1(i) \/ w2(i) \/ cs(i) \/ exit(i)

proc(i) == ncs(i) \/ NonNcs(i)

Next == \E i \in Procs : proc(i)

\* Weak fairness on every step except the non-critical section:
\* a process may remain in its non-critical section forever.
Fairness == \A i \in Procs : WF_vars(NonNcs(i))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
\* Bound on ticket numbers, usable as a TLC state constraint.
TicketBound == \A i \in Procs : num[i] <= MaxNat

\* Safety: at most one process is in the critical section.
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: if some process is trying, some process eventually enters CS.
DeadlockFreedom ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E i \in Procs : pc[i] = "cs")

\* Liveness: every process that requests entry eventually enters CS.
StarvationFreedom ==
    \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom /\ StarvationFreedom
===========================================================================
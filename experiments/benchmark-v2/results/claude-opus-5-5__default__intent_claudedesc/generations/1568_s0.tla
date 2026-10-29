---------------------------- MODULE Bakery ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N,          \* number of processes
          MaxTicket   \* bound on ticket values for finite-state checking

ASSUME /\ N \in Nat \ {0}
       /\ MaxTicket \in Nat \ {0}

Procs == 1..N

VARIABLES num,        \* num[i]       : ticket number of process i (0 = no ticket)
          choosing,   \* choosing[i]  : TRUE while process i is choosing a ticket
          pc,         \* pc[i]        : control location of process i
          unchecked,  \* unchecked[i] : processes not yet examined by i in a scan/wait loop
          mx,         \* mx[i]        : maximum ticket seen so far by i
          nxt         \* nxt[i]       : process i is currently waiting on

vars == <<num, choosing, pc, unchecked, mx, nxt>>

Labels == {"ncs", "e1", "e2", "e3", "w1", "w2", "cs", "exit"}

\* Lexicographic priority: (num[i], i) < (num[j], j)
Before(i, j) == \/ num[i] < num[j]
                \/ /\ num[i] = num[j]
                   /\ i < j

TypeOK ==
    /\ num       \in [Procs -> 0..MaxTicket]
    /\ choosing  \in [Procs -> BOOLEAN]
    /\ pc        \in [Procs -> Labels]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ mx        \in [Procs -> 0..MaxTicket]
    /\ nxt       \in [Procs -> Procs]

Init ==
    /\ num       = [i \in Procs |-> 0]
    /\ choosing  = [i \in Procs |-> FALSE]
    /\ pc        = [i \in Procs |-> "ncs"]
    /\ unchecked = [i \in Procs |-> {}]
    /\ mx        = [i \in Procs |-> 0]
    /\ nxt       = [i \in Procs |-> i]

\* Non-critical section: start trying, signal choosing
ncs(i) ==
    /\ pc[i] = "ncs"
    /\ choosing'  = [choosing EXCEPT ![i] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
    /\ mx'        = [mx EXCEPT ![i] = 0]
    /\ pc'        = [pc EXCEPT ![i] = "e1"]
    /\ UNCHANGED <<num, nxt>>

\* Scan other processes' numbers one at a time to find the maximum
e1(i) ==
    /\ pc[i] = "e1"
    /\ IF unchecked[i] # {}
         THEN \E j \in unchecked[i] :
                /\ unchecked' = [unchecked EXCEPT ![i] = @ \ {j}]
                /\ mx' = [mx EXCEPT ![i] = IF num[j] > @ THEN num[j] ELSE @]
                /\ UNCHANGED pc
         ELSE /\ pc' = [pc EXCEPT ![i] = "e2"]
              /\ UNCHANGED <<unchecked, mx>>
    /\ UNCHANGED <<num, choosing, nxt>>

\* Set own number to one more than the maximum (bounded for model checking)
e2(i) ==
    /\ pc[i] = "e2"
    /\ mx[i] + 1 <= MaxTicket
    /\ num' = [num EXCEPT ![i] = mx[i] + 1]
    /\ pc'  = [pc EXCEPT ![i] = "e3"]
    /\ UNCHANGED <<choosing, unchecked, mx, nxt>>

\* Clear choosing flag and prepare to wait on all other processes
e3(i) ==
    /\ pc[i] = "e3"
    /\ choosing'  = [choosing EXCEPT ![i] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![i] = Procs \ {i}]
    /\ pc'        = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<num, mx, nxt>>

\* Pick a not-yet-checked process j and wait until it is not choosing;
\* when all have been checked, enter the critical section
w1(i) ==
    /\ pc[i] = "w1"
    /\ IF unchecked[i] # {}
         THEN \E j \in unchecked[i] :
                /\ ~choosing[j]
                /\ nxt' = [nxt EXCEPT ![i] = j]
                /\ pc'  = [pc EXCEPT ![i] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![i] = "cs"]
              /\ UNCHANGED nxt
    /\ UNCHANGED <<num, choosing, unchecked, mx>>

\* Wait until i has priority over nxt[i]
w2(i) ==
    /\ pc[i] = "w2"
    /\ LET j == nxt[i] IN
         /\ \/ num[j] = 0
            \/ Before(i, j)
         /\ unchecked' = [unchecked EXCEPT ![i] = @ \ {j}]
    /\ pc' = [pc EXCEPT ![i] = "w1"]
    /\ UNCHANGED <<num, choosing, mx, nxt>>

\* Critical section (no-op placeholder)
cs(i) ==
    /\ pc[i] = "cs"
    /\ TRUE
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<num, choosing, unchecked, mx, nxt>>

\* Exit: release ticket and return to non-critical section
exit(i) ==
    /\ pc[i] = "exit"
    /\ num' = [num EXCEPT ![i] = 0]
    /\ pc'  = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<choosing, unchecked, mx, nxt>>

proc(i) == ncs(i) \/ e1(i) \/ e2(i) \/ e3(i) \/ w1(i) \/ w2(i) \/ cs(i) \/ exit(i)

Next == \E i \in Procs : proc(i)

Spec == Init /\ [][Next]_vars

\* Optional fairness: every process that leaves its non-critical section
\* keeps taking steps (bounded tickets may still block e2 when MaxTicket is reached)
FairSpec == Spec /\ \A i \in Procs : WF_vars(proc(i) /\ pc[i] # "ncs")

-----------------------------------------------------------------------------
\* Safety: mutual exclusion
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness (under FairSpec): a process that tries eventually enters the CS
StarvationFree ==
    \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================
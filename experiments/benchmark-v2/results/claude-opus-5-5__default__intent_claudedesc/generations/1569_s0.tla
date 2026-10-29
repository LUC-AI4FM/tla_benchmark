---- MODULE Bakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxTicket

ASSUME NAssump == N \in Nat /\ N >= 1
ASSUME MaxAssump == MaxTicket \in Nat

Procs == 1..N

\* Lexicographic order on <<ticket, processId>> pairs, used to break ties by process ID
a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1] /\ a[2] < b[2])

VARIABLES num, flag, pc, unchecked, max, nxt

vars == << num, flag, pc, unchecked, max, nxt >>

TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ flag \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "w1", "w2", "cs", "exit"}]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ max \in [Procs -> Nat]
    /\ nxt \in [Procs -> Procs]

Init ==
    /\ num = [i \in Procs |-> 0]
    /\ flag = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ unchecked = [i \in Procs |-> {}]
    /\ max = [i \in Procs |-> 0]
    /\ nxt = [i \in Procs |-> i]

\* Non-critical section: decide to try to enter the critical section
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

\* Start choosing: raise the choosing flag and prepare to scan all other processes
e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << num, nxt >>

\* Read the tickets of other processes one at a time, in nondeterministic order
e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unchecked[self] # {}
          THEN /\ \E i \in unchecked[self] :
                    /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                    /\ IF num[i] > max[self]
                          THEN max' = [max EXCEPT ![self] = num[i]]
                          ELSE max' = max
               /\ pc' = [pc EXCEPT ![self] = "e2"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
               /\ UNCHANGED << unchecked, max >>
    /\ UNCHANGED << num, flag, nxt >>

\* Take a ticket one higher than the maximum observed
e3(self) ==
    /\ pc[self] = "e3"
    /\ num' = [num EXCEPT ![self] = max[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

\* Finish choosing: lower the flag and prepare to scan for the waiting phase
e4(self) ==
    /\ pc[self] = "e4"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

\* Pick another process (nondeterministically) and wait until it is not choosing
w1(self) ==
    /\ pc[self] = "w1"
    /\ IF unchecked[self] # {}
          THEN /\ \E i \in unchecked[self] :
                    nxt' = [nxt EXCEPT ![self] = i]
               /\ ~ flag[nxt'[self]]
               /\ pc' = [pc EXCEPT ![self] = "w2"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ nxt' = nxt
    /\ UNCHANGED << num, flag, unchecked, max >>

\* Wait until the selected process has no ticket or has a larger (ticket, id) pair
w2(self) ==
    /\ pc[self] = "w2"
    /\ \/ num[nxt[self]] = 0
       \/ << num[self], self >> \prec << num[nxt[self]], nxt[self] >>
    /\ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, flag, max, nxt >>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

\* Exit: reset the ticket to zero and return to the non-critical section
exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

p(self) ==
    \/ ncs(self)
    \/ e1(self)
    \/ e2(self)
    \/ e3(self)
    \/ e4(self)
    \/ w1(self)
    \/ w2(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : p(self)

\* Every process that has left its non-critical section keeps taking steps.
\* A process may remain in its non-critical section forever.
Fairness == \A self \in Procs : WF_vars((pc[self] # "ncs") /\ p(self))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------

\* Safety: at most one process is in the critical section at any time
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: every process that tries to enter eventually enters the critical section
StarvationFree ==
    \A i \in Procs : (pc[i] = "e1") ~> (pc[i] = "cs")

\* Liveness: if some process is trying, some process eventually enters
DeadlockFree ==
    (\E i \in Procs : pc[i] \in {"e1", "e2", "e3", "e4", "w1", "w2"})
        ~> (\E i \in Procs : pc[i] = "cs")

\* State constraint for TLC: bound the ticket values
TicketConstraint == \A i \in Procs : num[i] <= MaxTicket

THEOREM Spec => [](TypeOK /\ MutualExclusion)
====
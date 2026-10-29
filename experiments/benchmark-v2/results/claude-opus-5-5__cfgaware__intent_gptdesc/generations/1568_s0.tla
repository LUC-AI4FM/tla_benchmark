---- MODULE Bakery ----
EXTENDS Naturals, FiniteSets

\* Lamport's Bakery algorithm for NumProcs threads.
\* Fairness assumption: every thread step is weakly fair. The non-critical
\* section is modeled as an immediate retry.

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs >= 1
ASSUME MaxNum \in Nat /\ MaxNum >= 1

Procs == 1 .. NumProcs

VARIABLES num, flag, unchecked, max, nxt, pc

vars == << num, flag, unchecked, max, nxt, pc >>

Labels == {"e1", "e2", "e3", "e4", "w1", "w2", "w3", "cs", "exit"}

\* Lexicographic priority on <<ticket, id>>.
Prec(i, j) == \/ num[i] < num[j]
              \/ (num[i] = num[j] /\ i < j)

TypeOK ==
    /\ num \in [Procs -> Nat]
    /\ flag \in [Procs -> BOOLEAN]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ max \in [Procs -> Nat]
    /\ nxt \in [Procs -> Procs]
    /\ pc \in [Procs -> Labels]

Init ==
    /\ num = [p \in Procs |-> 0]
    /\ flag = [p \in Procs |-> FALSE]
    /\ unchecked = [p \in Procs |-> {}]
    /\ max = [p \in Procs |-> 0]
    /\ nxt = [p \in Procs |-> 1]
    /\ pc = [p \in Procs |-> "e1"]

\* Signal that this thread is choosing a ticket.
e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << num, nxt >>

\* Compute the maximum ticket among peers, one peer at a time.
e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {i}]
                /\ IF num[i] > max[self]
                     THEN max' = [max EXCEPT ![self] = num[i]]
                     ELSE UNCHANGED max
                /\ UNCHANGED pc
         ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
              /\ UNCHANGED << unchecked, max >>
    /\ UNCHANGED << num, flag, nxt >>

\* Take a ticket one greater than the observed maximum.
e3(self) ==
    /\ pc[self] = "e3"
    /\ num' = [num EXCEPT ![self] = max[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

ChooseNumber == \E self \in Procs : e3(self)

\* Finish choosing.
e4(self) ==
    /\ pc[self] = "e4"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, max, nxt >>

\* Pick the next peer to wait for, or enter the critical section.
w1(self) ==
    /\ pc[self] = "w1"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ nxt' = [nxt EXCEPT ![self] = i]
                /\ pc' = [pc EXCEPT ![self] = "w2"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED nxt
    /\ UNCHANGED << num, flag, unchecked, max >>

\* Wait until that peer is not choosing.
w2(self) ==
    /\ pc[self] = "w2"
    /\ ~flag[nxt[self]]
    /\ pc' = [pc EXCEPT ![self] = "w3"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

\* Wait until that peer has no priority.
w3(self) ==
    /\ pc[self] = "w3"
    /\ \/ num[nxt[self]] = 0
       \/ Prec(self, nxt[self])
    /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {nxt[self]}]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED << num, flag, max, nxt >>

\* Critical section.
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << num, flag, unchecked, max, nxt >>

\* Reset the ticket and repeat.
exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, unchecked, max, nxt >>

proc(self) == \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
              \/ w1(self) \/ w2(self) \/ w3(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : proc(self)

\* Fairness assumption: weak fairness for every thread.
Fairness == \A self \in Procs : WF_vars(proc(self))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------

\* Set of threads currently in the critical section.
InCS == {p \in Procs : pc[p] = "cs"}

PossibleCounts == {0, 1}

\* Safety: at most one thread is in the critical section.
MutualExclusion == Cardinality(InCS) <= 1

_POSSIBLE == Cardinality(InCS) \in PossibleCounts

Invariant == TypeOK /\ MutualExclusion

\* Boundedness: state constraint used for model checking.
Constraint == \A p \in Procs : num[p] <= MaxNum

TicketsBounded == \A p \in Procs : num[p] <= MaxNum

Trying(p) == pc[p] \in {"e1", "e2", "e3", "e4", "w1", "w2", "w3"}

\* Absence of deadlock: some thread can always step while one is trying.
DeadlockFree == (\E p \in Procs : Trying(p)) => ENABLED Next

\* Liveness: starvation freedom under weak fairness.
StarvationFree == \A p \in Procs : Trying(p) ~> (pc[p] = "cs")

\* Progress: some thread eventually enters the critical section.
Progress == (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : pc[p] = "cs")

Liveness == StarvationFree /\ Progress

THEOREM Spec => [](Invariant /\ DeadlockFree)
====
------------------------------ MODULE Bakery ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS N, MaxTicket

ASSUME N \in Nat /\ N > 0
ASSUME MaxTicket \in Nat /\ MaxTicket > 0

Procs == 1..N

VARIABLES pc, num, flag, nxt, previous

vars == <<pc, num, flag, nxt, previous>>

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "cs", "exit"}]
    /\ num \in [Procs -> Nat]
    /\ flag \in [Procs -> BOOLEAN]
    /\ nxt \in [Procs -> Procs]
    /\ previous \in [Procs -> Nat]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ num = [p \in Procs |-> 0]
    /\ flag = [p \in Procs |-> FALSE]
    /\ nxt = [p \in Procs |-> 1]
    /\ previous = [p \in Procs |-> 0]

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

MaxNum == Max({num[p] : p \in Procs})

\* Non-critical section - process decides to enter
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED <<num, flag, nxt, previous>>

\* Entry phase 1: raise flag
e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED <<num, nxt, previous>>

\* Entry phase 2: take a ticket number
e2(self) ==
    /\ pc[self] = "e2"
    /\ num' = [num EXCEPT ![self] = MaxNum + 1]
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ nxt' = [nxt EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "e3"]
    /\ UNCHANGED <<previous>>

\* Entry phase 3: check if done waiting for all processes
e3(self) ==
    /\ pc[self] = "e3"
    /\ IF nxt[self] > N
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<num, flag, nxt, previous>>
       ELSE /\ previous' = [previous EXCEPT ![self] = num[nxt[self]]]
            /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED <<num, flag, nxt>>

\* Entry phase 4: wait for process nxt[self]
e4(self) ==
    /\ pc[self] = "e4"
    /\ \/ flag[nxt[self]] = FALSE /\ 
          (num[nxt[self]] = 0 \/ 
           num[self] < num[nxt[self]] \/ 
           (num[self] = num[nxt[self]] /\ self < nxt[self]))
       \/ /\ flag[nxt[self]] = FALSE
          /\ previous[self] # num[nxt[self]]
    /\ nxt' = [nxt EXCEPT ![self] = nxt[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "e3"]
    /\ UNCHANGED <<num, flag, previous>>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<num, flag, nxt, previous>>

\* Exit: reset ticket number
exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<flag, nxt, previous>>

\* Process action
proc(self) ==
    \/ ncs(self)
    \/ e1(self)
    \/ e2(self)
    \/ e3(self)
    \/ e4(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : proc(self)

\* Fairness: weak fairness for each process action
Fairness == \A self \in Procs : WF_vars(proc(self))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Mutual Exclusion: no two processes in critical section simultaneously
MutualExclusion == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* At most one process in critical section
AtMostOneInCS == Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

\* Constraint for TLC: bound ticket numbers
TicketConstraint == \A p \in Procs : num[p] <= MaxTicket

\* Liveness: if a process wants to enter, it eventually enters CS
Liveness == \A p \in Procs : (pc[p] = "e1") ~> (pc[p] = "cs")

\* Starvation freedom: a process trying to enter will eventually enter
StarvationFreedom == \A p \in Procs : (pc[p] \in {"e1", "e2", "e3", "e4"}) ~> (pc[p] = "cs")

=============================================================================
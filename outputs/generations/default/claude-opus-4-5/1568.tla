-------------------------------- MODULE Bakery --------------------------------
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

\* Non-critical section - move to doorway
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "e1"]
    /\ UNCHANGED <<num, flag, nxt, previous>>

\* Doorway: set flag
E1(p) ==
    /\ pc[p] = "e1"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "e2"]
    /\ UNCHANGED <<num, nxt, previous>>

\* Take a ticket number
E2(p) ==
    /\ pc[p] = "e2"
    /\ num' = [num EXCEPT ![p] = MaxNum + 1]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ nxt' = [nxt EXCEPT ![p] = 1]
    /\ pc' = [pc EXCEPT ![p] = "e3"]
    /\ UNCHANGED <<previous>>

\* Wait for other processes - check if done with all
E3(p) ==
    /\ pc[p] = "e3"
    /\ IF nxt[p] > N
       THEN /\ pc' = [pc EXCEPT ![p] = "cs"]
            /\ UNCHANGED <<num, flag, nxt, previous>>
       ELSE /\ previous' = [previous EXCEPT ![p] = num[nxt[p]]]
            /\ pc' = [pc EXCEPT ![p] = "e4"]
            /\ UNCHANGED <<num, flag, nxt>>

\* Compare with process nxt[p]
\* (num[p], p) << (num[q], q) means num[p] < num[q] \/ (num[p] = num[q] /\ p < q)
Before(i, j) ==
    \/ num[i] < num[j]
    \/ (num[i] = num[j] /\ i < j)

E4(p) ==
    /\ pc[p] = "e4"
    /\ LET q == nxt[p]
       IN /\ flag[q] = FALSE
          /\ \/ num[q] = 0
             \/ Before(p, q)
             \/ num[q] # previous[p]
    /\ nxt' = [nxt EXCEPT ![p] = nxt[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "e3"]
    /\ UNCHANGED <<num, flag, previous>>

\* Critical section - move to exit
CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<num, flag, nxt, previous>>

\* Exit: reset ticket number
Exit(p) ==
    /\ pc[p] = "exit"
    /\ num' = [num EXCEPT ![p] = 0]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED <<flag, nxt, previous>>

proc(p) ==
    \/ NCS(p)
    \/ E1(p)
    \/ E2(p)
    \/ E3(p)
    \/ E4(p)
    \/ CS(p)
    \/ Exit(p)

Next == \E p \in Procs : proc(p)

\* Fairness: weak fairness for each process action
Fairness == \A p \in Procs : WF_vars(proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Mutual Exclusion
MutualExclusion == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* State constraint for model checking
TicketConstraint == \A p \in Procs : num[p] <= MaxTicket

\* Liveness: Every process that wants to enter CS eventually does
Liveness == \A p \in Procs : (pc[p] = "e1") ~> (pc[p] = "cs")

\* Starvation freedom
StarvationFreedom == \A p \in Procs : (pc[p] # "ncs") ~> (pc[p] = "cs")

================================================================================
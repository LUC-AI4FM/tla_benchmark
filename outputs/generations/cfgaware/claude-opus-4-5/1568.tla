-------------------------------- MODULE Bakery --------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT NumProcs, MaxTicket

VARIABLES pc, num, flag, i, localj

vars == <<pc, num, flag, i, localj>>

Procs == 1..NumProcs

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "cs", "exit"}]
    /\ num \in [Procs -> 0..MaxTicket]
    /\ flag \in [Procs -> BOOLEAN]
    /\ i \in [Procs -> Procs]
    /\ localj \in [Procs -> 1..(NumProcs+1)]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ num = [p \in Procs |-> 0]
    /\ flag = [p \in Procs |-> FALSE]
    /\ i = [p \in Procs |-> 1]
    /\ localj = [p \in Procs |-> 1]

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED <<num, flag, i, localj>>

e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED <<num, i, localj>>

e2(self) ==
    /\ pc[self] = "e2"
    /\ LET maxNum == IF {num[q] : q \in Procs} = {} 
                     THEN 0 
                     ELSE Max({num[q] : q \in Procs})
       IN /\ num' = [num EXCEPT ![self] = maxNum + 1]
          /\ localj' = [localj EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "e3"]
    /\ UNCHANGED <<flag, i>>

e3(self) ==
    /\ pc[self] = "e3"
    /\ IF localj[self] <= NumProcs
       THEN /\ pc' = [pc EXCEPT ![self] = "e4"]
            /\ UNCHANGED <<num, flag, i, localj>>
       ELSE /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<num, i, localj>>

e4(self) ==
    /\ pc[self] = "e4"
    /\ IF localj[self] = self
       THEN /\ localj' = [localj EXCEPT ![self] = localj[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED <<num, flag, i>>
       ELSE /\ \/ flag[localj[self]] = FALSE
               \/ /\ num[localj[self]] = 0
               \/ /\ num[localj[self]] > num[self]
               \/ /\ num[localj[self]] = num[self] /\ localj[self] > self
            /\ localj' = [localj EXCEPT ![self] = localj[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "e3"]
            /\ UNCHANGED <<num, flag, i>>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<num, flag, i, localj>>

exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<flag, i, localj>>

proc(self) ==
    \/ ncs(self)
    \/ e1(self)
    \/ e2(self)
    \/ e3(self)
    \/ e4(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : proc(self)

Fairness == \A self \in Procs : WF_vars(proc(self))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p1, p2 \in Procs : (p1 # p2) => ~(pc[p1] = "cs" /\ pc[p2] = "cs")

TicketBound ==
    \A p \in Procs : num[p] <= MaxTicket

Invariant == TypeOK /\ MutualExclusion /\ TicketBound

================================================================================
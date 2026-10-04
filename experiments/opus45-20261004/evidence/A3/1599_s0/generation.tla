--------------------------- MODULE FastMutex ---------------------------
EXTENDS Integers, TLAPS, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

ProcSet == 1..N

Locations == {"ncs", "start", "setx", "checkb", "sety", "checky", 
              "setb", "checkx", "wait", "cs", "exit1", "exit2"}

TypeOK == /\ x \in (0..N)
          /\ y \in (0..N)
          /\ b \in [1..N -> BOOLEAN]
          /\ pc \in [1..N -> Locations]

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ pc = [i \in 1..N |-> "ncs"]

\* Noncritical section - process can skip to start entry protocol
ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED <<x, y, b>>

\* Start entry protocol - set intent flag b[self] to TRUE
start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "setx"]
               /\ UNCHANGED <<x, y>>

\* Fast path - set x to self
setx(self) == /\ pc[self] = "setx"
              /\ x' = self
              /\ pc' = [pc EXCEPT ![self] = "checkb"]
              /\ UNCHANGED <<y, b>>

\* Check if y is 0 (no one claimed fast path yet)
checkb(self) == /\ pc[self] = "checkb"
                /\ IF y /= 0
                   THEN pc' = [pc EXCEPT ![self] = "setb"]
                   ELSE pc' = [pc EXCEPT ![self] = "sety"]
                /\ UNCHANGED <<x, y, b>>

\* Set y to self to claim fast path
sety(self) == /\ pc[self] = "sety"
              /\ y' = self
              /\ pc' = [pc EXCEPT ![self] = "checky"]
              /\ UNCHANGED <<x, b>>

\* Check if x still equals self (fast path success) or go to slow path
checky(self) == /\ pc[self] = "checky"
                /\ IF x /= self
                   THEN pc' = [pc EXCEPT ![self] = "setb"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs"]
                /\ UNCHANGED <<x, y, b>>

\* Slow path - clear own flag and check others
setb(self) == /\ pc[self] = "setb"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "checkx"]
              /\ UNCHANGED <<x, y>>

\* Check if y equals self (slow path success condition)
checkx(self) == /\ pc[self] = "checkx"
                /\ IF y /= self
                   THEN pc' = [pc EXCEPT ![self] = "start"]
                   ELSE pc' = [pc EXCEPT ![self] = "wait"]
                /\ UNCHANGED <<x, y, b>>

\* Wait until all other processes have cleared their b flags
wait(self) == /\ pc[self] = "wait"
              /\ \A j \in 1..N \ {self} : ~b[j]
              /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED <<x, y, b>>

\* Critical section - process can skip to exit
cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "exit1"]
            /\ UNCHANGED <<x, y, b>>

\* Exit protocol - clear y
exit1(self) == /\ pc[self] = "exit1"
               /\ y' = 0
               /\ pc' = [pc EXCEPT ![self] = "exit2"]
               /\ UNCHANGED <<x, b>>

\* Exit protocol - clear own b flag
exit2(self) == /\ pc[self] = "exit2"
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
               /\ UNCHANGED <<x, y>>

\* Individual process actions
proc(self) == ncs(self) \/ start(self) \/ setx(self) \/ checkb(self) 
              \/ sety(self) \/ checky(self) \/ setb(self) \/ checkx(self) 
              \/ wait(self) \/ cs(self) \/ exit1(self) \/ exit2(self)

Next == \E self \in ProcSet : proc(self)

\* Basic specification without fairness
Spec == Init /\ [][Next]_vars

\* Fairness for each control-location action except ncs and cs
FairSpec == Spec /\ \A self \in ProcSet : 
                    /\ WF_vars(start(self))
                    /\ WF_vars(setx(self))
                    /\ WF_vars(checkb(self))
                    /\ WF_vars(sety(self))
                    /\ WF_vars(checky(self))
                    /\ WF_vars(setb(self))
                    /\ WF_vars(checkx(self))
                    /\ WF_vars(wait(self))
                    /\ WF_vars(exit1(self))
                    /\ WF_vars(exit2(self))

\* Safety: Mutual Exclusion - no two distinct processes in CS simultaneously
MutualExclusion == \A i, j \in ProcSet : 
                     (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Alternative formulation
AtMostOneInCS == Cardinality({i \in ProcSet : pc[i] = "cs"}) <= 1

\* Liveness: Every process trying to enter CS eventually enters
Liveness == \A self \in ProcSet : 
              (pc[self] = "start") ~> (pc[self] = "cs")

\* Conditional Liveness: If a process is waiting, it eventually enters CS
ConditionalLiveness == \A self \in ProcSet :
                         (pc[self] = "wait") ~> (pc[self] = "cs")

\* Starvation freedom: Every process that starts entry protocol eventually returns to ncs
StarvationFreedom == \A self \in ProcSet :
                       (pc[self] /= "ncs") ~> (pc[self] = "ncs")

==========================================================================
---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

ProcSet == 1..N

Locs == {"ncs", "start", "setx", "checkb", "sety", "checkx", "checky", "cs", "exit1", "exit2"}

TypeOK ==
    /\ x \in ProcSet \cup {0}
    /\ y \in ProcSet \cup {0}
    /\ b \in [ProcSet -> BOOLEAN]
    /\ pc \in [ProcSet -> Locs]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ pc = [i \in ProcSet |-> "ncs"]

\* Noncritical section - process decides to enter critical section
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b>>

\* Start: set b[self] to TRUE to indicate intent
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y>>

\* Set x to self
setx(self) ==
    /\ pc[self] = "setx"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checkb"]
    /\ UNCHANGED <<y, b>>

\* Check if y is 0; if not, reset b and go back to start
checkb(self) ==
    /\ pc[self] = "checkb"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "checky"]
            /\ UNCHANGED <<x, y>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
            /\ UNCHANGED <<x, y, b>>

\* Wait for y to become 0, then go back to start
checky(self) ==
    /\ pc[self] = "checky"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b>>

\* Set y to self
sety(self) ==
    /\ pc[self] = "sety"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<x, b>>

\* Check if x equals self
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "waitb"]
            /\ UNCHANGED <<x, y>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b>>

\* Wait for all other processes to clear their b flags
waitb(self) ==
    /\ pc[self] = "waitb"
    /\ \A j \in ProcSet \ {self} : ~b[j]
    /\ IF y = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "checky2"]
    /\ UNCHANGED <<x, y, b>>

\* Wait for y to become 0, then restart
checky2(self) ==
    /\ pc[self] = "checky2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b>>

\* Critical section - process is in critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit1"]
    /\ UNCHANGED <<x, y, b>>

\* Exit: clear y
exit1(self) ==
    /\ pc[self] = "exit1"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "exit2"]
    /\ UNCHANGED <<x, b>>

\* Exit: clear b[self]
exit2(self) ==
    /\ pc[self] = "exit2"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, y>>

\* Combined process actions
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setx(self)
    \/ checkb(self)
    \/ checky(self)
    \/ sety(self)
    \/ checkx(self)
    \/ waitb(self)
    \/ checky2(self)
    \/ cs(self)
    \/ exit1(self)
    \/ exit2(self)

Next == \E self \in ProcSet : proc(self)

\* Specification without fairness
Spec == Init /\ [][Next]_vars

\* Weak fairness for control-location actions except ncs and cs
FairSpec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in ProcSet :
        /\ WF_vars(start(self))
        /\ WF_vars(setx(self))
        /\ WF_vars(checkb(self))
        /\ WF_vars(checky(self))
        /\ WF_vars(sety(self))
        /\ WF_vars(checkx(self))
        /\ WF_vars(waitb(self))
        /\ WF_vars(checky2(self))
        /\ WF_vars(exit1(self))
        /\ WF_vars(exit2(self))

\* Safety: Mutual Exclusion
MutualExclusion ==
    \A i, j \in ProcSet : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Alternative formulation
MutEx == \A i \in ProcSet : \A j \in ProcSet : (pc[i] = "cs" /\ pc[j] = "cs") => (i = j)

\* Liveness: every process that starts trying eventually enters the critical section
Liveness == \A self \in ProcSet : (pc[self] = "start") ~> (pc[self] = "cs")

\* Conditional liveness: if a process leaves ncs, it eventually enters cs
ConditionalLiveness == \A self \in ProcSet : (pc[self] /= "ncs") ~> (pc[self] = "cs")

\* Starvation freedom
StarvationFreedom == \A self \in ProcSet : (pc[self] = "start") ~> (pc[self] = "cs")

==========================================================================
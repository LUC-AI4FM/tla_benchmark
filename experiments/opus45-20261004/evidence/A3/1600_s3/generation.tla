-------------------------------- MODULE FastMutex --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLAPS

CONSTANTS N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc, j, failed

vars == <<x, y, b, pc, j, failed>>

Procs == 1..N

TypeOK ==
    /\ x \in Procs \cup {0}
    /\ y \in Procs \cup {0}
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "start", "setb", "setx", "checky", "sety", 
                         "checkx", "wait", "cs", "exit1", "exit2"}]
    /\ j \in [Procs -> Procs \cup {0}]
    /\ failed \in [Procs -> BOOLEAN]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ j = [i \in Procs |-> 0]
    /\ failed = [i \in Procs |-> FALSE]

\* Non-critical section - process decides to enter
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, j, failed>>

\* Start - reset failed flag
start(self) ==
    /\ pc[self] = "start"
    /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "setb"]
    /\ UNCHANGED <<x, y, b, j>>

\* Set intent flag b[self] to TRUE
setb(self) ==
    /\ pc[self] = "setb"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y, j, failed>>

\* Set x to self
setx(self) ==
    /\ pc[self] = "setx"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checky"]
    /\ UNCHANGED <<y, b, j, failed>>

\* Check if y is 0 (no one else succeeded in fast path)
checky(self) ==
    /\ pc[self] = "checky"
    /\ IF y /= 0
       THEN /\ failed' = [failed EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "checkx"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
            /\ UNCHANGED failed
    /\ UNCHANGED <<x, y, b, j>>

\* Set y to self (claim the lock via fast path)
sety(self) ==
    /\ pc[self] = "sety"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<x, b, j, failed>>

\* Check if x is still self (no one overwrote x)
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ IF x /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "wait"]
            /\ j' = [j EXCEPT ![self] = 1]
       ELSE /\ IF failed[self]
               THEN /\ pc' = [pc EXCEPT ![self] = "wait"]
                    /\ j' = [j EXCEPT ![self] = 1]
               ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                    /\ UNCHANGED j
    /\ UNCHANGED <<x, y, b, failed>>

\* Wait for other processes to clear their intent flags
wait(self) ==
    /\ pc[self] = "wait"
    /\ IF j[self] <= N
       THEN IF j[self] = self
            THEN /\ j' = [j EXCEPT ![self] = j[self] + 1]
                 /\ UNCHANGED pc
            ELSE IF b[j[self]] = FALSE
                 THEN /\ j' = [j EXCEPT ![self] = j[self] + 1]
                      /\ UNCHANGED pc
                 ELSE UNCHANGED <<pc, j>>
       ELSE IF y = self
            THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                 /\ UNCHANGED j
            ELSE /\ pc' = [pc EXCEPT ![self] = "exit1"]
                 /\ UNCHANGED j
    /\ UNCHANGED <<x, y, b, failed>>

\* Critical section - process is in CS
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit1"]
    /\ UNCHANGED <<x, y, b, j, failed>>

\* Exit - clear y
exit1(self) ==
    /\ pc[self] = "exit1"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "exit2"]
    /\ UNCHANGED <<x, b, j, failed>>

\* Exit - clear intent flag
exit2(self) ==
    /\ pc[self] = "exit2"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, y, j, failed>>

\* Process action combining all actions for a single process
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setb(self)
    \/ setx(self)
    \/ checky(self)
    \/ sety(self)
    \/ checkx(self)
    \/ wait(self)
    \/ cs(self)
    \/ exit1(self)
    \/ exit2(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Procs : WF_vars(proc(self))

\* Safety: Mutual Exclusion - at most one process in critical section
MutualExclusion ==
    \A i, k \in Procs : (pc[i] = "cs" /\ pc[k] = "cs") => i = k

\* Alternative formulation of mutual exclusion
AtMostOneInCS == Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

\* Liveness: Some process enters the critical section infinitely often
SomeoneEntersCS == []<>(\E i \in Procs : pc[i] = "cs")

===============================================================================
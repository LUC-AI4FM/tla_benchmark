---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS, TLC, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc, j, failed

vars == <<x, y, b, pc, j, failed>>

ProcSet == 1..N

Init == 
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ pc = [i \in ProcSet |-> "ncs"]
    /\ j = [i \in ProcSet |-> 1]
    /\ failed = [i \in ProcSet |-> FALSE]

(* Non-critical section - process starts attempt to enter critical section *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, j, failed>>

(* Start: set intent flag b[self] to TRUE *)
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y, j, failed>>

(* Set x to self *)
setx(self) ==
    /\ pc[self] = "setx"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checky"]
    /\ UNCHANGED <<y, b, j, failed>>

(* Check if y is 0 *)
checky(self) ==
    /\ pc[self] = "checky"
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![self] = "sety"]
       ELSE pc' = [pc EXCEPT ![self] = "slowpath"]
    /\ UNCHANGED <<x, y, b, j, failed>>

(* Fast path: set y to self *)
sety(self) ==
    /\ pc[self] = "sety"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<x, b, j, failed>>

(* Check if x still equals self *)
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ IF x = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "clearb"]
            /\ failed' = [failed EXCEPT ![self] = TRUE]
            /\ UNCHANGED <<x, y, b, j>>
    /\ IF x = self THEN UNCHANGED <<failed>> ELSE TRUE

(* Clear own b flag when fast path fails *)
clearb(self) ==
    /\ pc[self] = "clearb"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "waitloop"]
    /\ UNCHANGED <<x, y, failed>>

(* Wait for all other processes to clear their b flags *)
waitloop(self) ==
    /\ pc[self] = "waitloop"
    /\ IF j[self] <= N
       THEN IF j[self] # self /\ b[j[self]]
            THEN pc' = [pc EXCEPT ![self] = "waitloop"]
                 /\ UNCHANGED <<j>>
            ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "waitloop"]
       ELSE pc' = [pc EXCEPT ![self] = "checky2"]
            /\ UNCHANGED <<j>>
    /\ UNCHANGED <<x, y, b, failed>>

(* Check y again after waiting *)
checky2(self) ==
    /\ pc[self] = "checky2"
    /\ IF y = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "restart"]
    /\ UNCHANGED <<x, y, b, j, failed>>

(* Slow path: clear b and wait on y *)
slowpath(self) ==
    /\ pc[self] = "slowpath"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "waity"]
    /\ UNCHANGED <<x, y, j, failed>>

(* Wait until y becomes 0 *)
waity(self) ==
    /\ pc[self] = "waity"
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![self] = "start"]
       ELSE pc' = [pc EXCEPT ![self] = "waity"]
    /\ UNCHANGED <<x, y, b, j, failed>>

(* Restart after failed attempt *)
restart(self) ==
    /\ pc[self] = "restart"
    /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, j>>

(* Critical section - process is in critical section, then exits *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, j, failed>>

(* Exit: clear y and b, return to non-critical section *)
exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, j>>

(* Process action combining all steps for a single process *)
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setx(self)
    \/ checky(self)
    \/ sety(self)
    \/ checkx(self)
    \/ clearb(self)
    \/ waitloop(self)
    \/ checky2(self)
    \/ slowpath(self)
    \/ waity(self)
    \/ restart(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in ProcSet : proc(self)

Spec == Init /\ [][Next]_vars /\ \A self \in ProcSet : WF_vars(proc(self))

(* Safety: Mutual Exclusion - at most one process in critical section *)
MutualExclusion == \A i, k \in ProcSet : (pc[i] = "cs" /\ pc[k] = "cs") => i = k

(* Type invariant *)
TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [ProcSet -> BOOLEAN]
    /\ pc \in [ProcSet -> {"ncs", "start", "setx", "checky", "sety", "checkx", 
                           "clearb", "waitloop", "checky2", "slowpath", 
                           "waity", "restart", "cs", "exit"}]
    /\ j \in [ProcSet -> 1..(N+1)]
    /\ failed \in [ProcSet -> BOOLEAN]

(* Liveness: Some process enters critical section infinitely often *)
Liveness == []<>(\E self \in ProcSet : pc[self] = "cs")

==========================================================================
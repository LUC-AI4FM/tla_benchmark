---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS, TLC

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

(* Non-critical section - process decides to enter critical section *)
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
    /\ IF y /= 0
       THEN /\ pc' = [pc EXCEPT ![self] = "slowpath"]
            /\ failed' = [failed EXCEPT ![self] = TRUE]
       ELSE /\ pc' = [pc EXCEPT ![self] = "sety"]
            /\ failed' = [failed EXCEPT ![self] = FALSE]
    /\ UNCHANGED <<x, y, b, j>>

(* Set y to self (fast path) *)
sety(self) ==
    /\ pc[self] = "sety"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<x, b, j, failed>>

(* Check if x is still self *)
checkx(self) ==
    /\ pc[self] = "checkx"
    /\ IF x /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "slowpath"]
            /\ failed' = [failed EXCEPT ![self] = TRUE]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED failed
    /\ UNCHANGED <<x, y, b, j>>

(* Slow path: reset b[self] and start checking other processes *)
slowpath(self) ==
    /\ pc[self] = "slowpath"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "checkb"]
    /\ UNCHANGED <<x, y, failed>>

(* Check b[j] for all processes in slow path *)
checkb(self) ==
    /\ pc[self] = "checkb"
    /\ IF j[self] <= N
       THEN /\ IF b[j[self]]
               THEN /\ pc' = [pc EXCEPT ![self] = "waitb"]
               ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                    /\ pc' = pc
            /\ UNCHANGED <<x, y, b, failed>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "checky2"]
            /\ UNCHANGED <<x, y, b, j, failed>>

(* Wait for b[j] to become FALSE *)
waitb(self) ==
    /\ pc[self] = "waitb"
    /\ b[j[self]] = FALSE
    /\ j' = [j EXCEPT ![self] = j[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "checkb"]
    /\ UNCHANGED <<x, y, b, failed>>

(* Check y again after scanning all b flags *)
checky2(self) ==
    /\ pc[self] = "checky2"
    /\ IF y /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "start"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, j, failed>>

(* Critical section *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b, j, failed>>

(* Exit: reset y and b[self] *)
exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, j, failed>>

(* Process action for process self *)
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ setx(self)
    \/ checky(self)
    \/ sety(self)
    \/ checkx(self)
    \/ slowpath(self)
    \/ checkb(self)
    \/ waitb(self)
    \/ checky2(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in ProcSet: proc(self)

Spec == Init /\ [][Next]_vars /\ \A self \in ProcSet: WF_vars(proc(self))

(* Mutual exclusion invariant: at most one process in critical section *)
MutualExclusion == \A i, k \in ProcSet: (pc[i] = "cs" /\ pc[k] = "cs") => i = k

(* Type invariant *)
TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [ProcSet -> BOOLEAN]
    /\ pc \in [ProcSet -> {"ncs", "start", "setx", "checky", "sety", "checkx", 
                           "slowpath", "checkb", "waitb", "checky2", "cs", "exit"}]
    /\ j \in [ProcSet -> 1..(N+1)]
    /\ failed \in [ProcSet -> BOOLEAN]

(* Liveness: some process enters critical section infinitely often *)
Liveness == []<>(\E self \in ProcSet: pc[self] = "cs")

==========================================================================
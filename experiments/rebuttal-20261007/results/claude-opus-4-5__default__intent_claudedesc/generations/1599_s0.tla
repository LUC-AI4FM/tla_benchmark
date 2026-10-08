---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

Procs == 1..N

(* Process states:
   "ncs"  - non-critical section
   "start" - beginning of lock acquisition, set b[self] := TRUE
   "setx" - write identity to x
   "checky" - check if y = 0
   "sety" - write identity to y
   "checkx" - check if x = self
   "wait" - wait for all flags to be false (contention detected)
   "checky2" - recheck y after waiting
   "waitfory" - wait until y = self
   "cs"   - critical section
   "exit1" - exit: clear y
   "exit2" - exit: clear b[self]
*)

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "start", "setx", "checky", "sety", 
                         "checkx", "wait", "checky2", "waitfory", "cs", 
                         "exit1", "exit2"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]

(* Non-critical section: process decides to enter *)
EnterProtocol(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b>>

(* Start: set own flag to indicate interest *)
Start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "setx"]
    /\ UNCHANGED <<x, y>>

(* Set x to self *)
SetX(self) ==
    /\ pc[self] = "setx"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "checky"]
    /\ UNCHANGED <<y, b>>

(* Check if y = 0 *)
CheckY(self) ==
    /\ pc[self] = "checky"
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![self] = "sety"]
       ELSE pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED <<x, y, b>>

(* Set y to self (fast path) *)
SetY(self) ==
    /\ pc[self] = "sety"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "checkx"]
    /\ UNCHANGED <<x, b>>

(* Check if x still equals self (fast path verification) *)
CheckX(self) ==
    /\ pc[self] = "checkx"
    /\ IF x = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]  \* Fast path success
       ELSE pc' = [pc EXCEPT ![self] = "wait"]  \* Contention detected
    /\ UNCHANGED <<x, y, b>>

(* Wait for all other flags to become false *)
Wait(self) ==
    /\ pc[self] = "wait"
    /\ \A j \in Procs \ {self} : b[j] = FALSE
    /\ pc' = [pc EXCEPT ![self] = "checky2"]
    /\ UNCHANGED <<x, y, b>>

(* Recheck y after waiting *)
CheckY2(self) ==
    /\ pc[self] = "checky2"
    /\ IF y = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]  \* We own y, enter CS
       ELSE pc' = [pc EXCEPT ![self] = "waitfory"]  \* Wait for y owner
    /\ UNCHANGED <<x, y, b>>

(* Wait until y equals self (slow path) *)
WaitForY(self) ==
    /\ pc[self] = "waitfory"
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![self] = "start"]  \* Retry from beginning
       ELSE IF y = self
            THEN pc' = [pc EXCEPT ![self] = "cs"]  \* Enter CS
            ELSE pc' = [pc EXCEPT ![self] = "waitfory"]  \* Keep waiting
    /\ UNCHANGED <<x, y, b>>

(* Critical section: process is in CS, moves to exit *)
ExitCS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit1"]
    /\ UNCHANGED <<x, y, b>>

(* Exit phase 1: clear y *)
Exit1(self) ==
    /\ pc[self] = "exit1"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "exit2"]
    /\ UNCHANGED <<x, b>>

(* Exit phase 2: clear own flag *)
Exit2(self) ==
    /\ pc[self] = "exit2"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, y>>

(* All actions for a process *)
Process(self) ==
    \/ EnterProtocol(self)
    \/ Start(self)
    \/ SetX(self)
    \/ CheckY(self)
    \/ SetY(self)
    \/ CheckX(self)
    \/ Wait(self)
    \/ CheckY2(self)
    \/ WaitForY(self)
    \/ ExitCS(self)
    \/ Exit1(self)
    \/ Exit2(self)

Next == \E self \in Procs : Process(self)

(* Weak fairness for all process actions *)
Fairness == \A self \in Procs : WF_vars(Process(self))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety: Mutual Exclusion *)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* A process is trying to enter if it's not in ncs *)
Trying(self) == pc[self] # "ncs"

(* Someone is in the critical section *)
SomeoneInCS == \E i \in Procs : pc[i] = "cs"

(* Liveness: If some process is trying, eventually some process enters CS *)
(* This is expressed as: if there's always someone trying, then infinitely often someone is in CS *)
Liveness == (\E i \in Procs : Trying(i)) ~> SomeoneInCS

(* Alternative formulation: under the given fairness, if some process keeps trying,
   some process enters CS infinitely often *)
LivenessProperty == [](\E i \in Procs : Trying(i)) => []<>SomeoneInCS

==========================================================================
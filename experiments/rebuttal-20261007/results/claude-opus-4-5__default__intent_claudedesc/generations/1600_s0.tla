---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

(*
Process states (program counter values):
- "ncs"      : non-critical section
- "start"    : beginning of entry protocol, set b[self] := TRUE
- "write_x"  : write x := self
- "check_y"  : check if y = 0
- "write_y"  : fast path: write y := self
- "check_x"  : fast path: check if x = self
- "cs"       : critical section
- "exit1"    : exit: set y := 0
- "exit2"    : exit: set b[self] := FALSE
- "slow_clear" : slow path: set b[self] := FALSE after fast path interference
- "slow_wait"  : slow path: wait for all b[j] = FALSE for j # self
- "slow_check" : slow path: check if y = self
- "slow_retry" : slow path: wait for y = 0 before retry
*)

TypeOK ==
    /\ x \in (Procs \cup {0})
    /\ y \in (Procs \cup {0})
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "start", "write_x", "check_y", "write_y", 
                         "check_x", "cs", "exit1", "exit2",
                         "slow_clear", "slow_wait", "slow_check", "slow_retry"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]

(* Non-critical section: process decides to try entering CS *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b>>

(* Start: announce interest by setting b[self] := TRUE *)
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "write_x"]
    /\ UNCHANGED <<x, y>>

(* Write x := self *)
write_x(self) ==
    /\ pc[self] = "write_x"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "check_y"]
    /\ UNCHANGED <<y, b>>

(* Check if y = 0 to decide fast or slow path *)
check_y(self) ==
    /\ pc[self] = "check_y"
    /\ IF y = 0
       THEN pc' = [pc EXCEPT ![self] = "write_y"]
       ELSE pc' = [pc EXCEPT ![self] = "slow_clear"]
    /\ UNCHANGED <<x, y, b>>

(* Fast path: write y := self *)
write_y(self) ==
    /\ pc[self] = "write_y"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "check_x"]
    /\ UNCHANGED <<x, b>>

(* Fast path: check if x = self (no interference) *)
check_x(self) ==
    /\ pc[self] = "check_x"
    /\ IF x = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "slow_clear"]
    /\ UNCHANGED <<x, y, b>>

(* Slow path: clear own flag after interference detected *)
slow_clear(self) ==
    /\ pc[self] = "slow_clear"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "slow_wait"]
    /\ UNCHANGED <<x, y>>

(* Slow path: wait until all other flags are clear *)
slow_wait(self) ==
    /\ pc[self] = "slow_wait"
    /\ \A j \in Procs \ {self} : b[j] = FALSE
    /\ pc' = [pc EXCEPT ![self] = "slow_check"]
    /\ UNCHANGED <<x, y, b>>

(* Slow path: check if y = self (we won the slow path) *)
slow_check(self) ==
    /\ pc[self] = "slow_check"
    /\ IF y = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "slow_retry"]
    /\ UNCHANGED <<x, y, b>>

(* Slow path: wait for y = 0 before retrying *)
slow_retry(self) ==
    /\ pc[self] = "slow_retry"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b>>

(* Critical section: process is in CS, moves to exit *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit1"]
    /\ UNCHANGED <<x, y, b>>

(* Exit phase 1: clear y *)
exit1(self) ==
    /\ pc[self] = "exit1"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "exit2"]
    /\ UNCHANGED <<x, b>>

(* Exit phase 2: clear own flag and return to ncs *)
exit2(self) ==
    /\ pc[self] = "exit2"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, y>>

(* Action for process self *)
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ write_x(self)
    \/ check_y(self)
    \/ write_y(self)
    \/ check_x(self)
    \/ cs(self)
    \/ exit1(self)
    \/ exit2(self)
    \/ slow_clear(self)
    \/ slow_wait(self)
    \/ slow_check(self)
    \/ slow_retry(self)

Next == \E self \in Procs : proc(self)

(* Weak fairness for each process *)
Fairness == \A self \in Procs : WF_vars(proc(self))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety: Mutual exclusion - at most one process in CS *)
MutualExclusion ==
    \A i, j \in Procs : (pc[i] = "cs" /\ pc[j] = "cs") => (i = j)

(* Alternative formulation: cardinality of processes in CS <= 1 *)
MutexInvariant ==
    Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

(* Liveness: Some process infinitely often enters CS *)
Liveness == []<>(\E i \in Procs : pc[i] = "cs")

=========================================================================
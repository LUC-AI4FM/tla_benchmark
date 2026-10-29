------------------------------ MODULE OneBitMutex ------------------------------
(***************************************************************************)
(* One-bit mutual exclusion algorithm (Burns / Lamport) for N processes.  *)
(* Each process i owns a single shared bit x[i].  A process sets its bit  *)
(* to request entry, then checks every other process.  If it finds a      *)
(* lower-numbered process with its bit set, it backs off: it clears its   *)
(* own bit, waits for that process to clear its bit, and starts over.     *)
(* If it finds a higher-numbered process with its bit set, it waits for   *)
(* that process to clear its bit.                                         *)
(*                                                                         *)
(* Expected results: MutualExclusion and DeadlockFreedom hold.            *)
(* StarvationFreedom does NOT hold, because a higher-numbered process can *)
(* be overtaken forever by lower-numbered processes.                      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT N            \* number of processes; use N = 3 for model checking

ASSUME N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

VARIABLES
    x,          \* x[i] : the one-bit shared flag of process i
    pc,         \* pc[i] : control location of process i
    unchecked,  \* unchecked[i] : processes that i still has to examine
    other       \* other[i] : the process i is currently examining

vars == << x, pc, unchecked, other >>

Labels  == {"ncs", "e1", "e2", "e3", "e4", "e5", "e6", "cs", "f"}
Trying  == {"e1", "e2", "e3", "e4", "e5", "e6"}

TypeOK ==
    /\ x \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> Labels]
    /\ unchecked \in [Procs -> SUBSET Procs]
    /\ other \in [Procs -> Procs]

Init ==
    /\ x = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]
    /\ unchecked = [i \in Procs |-> {}]
    /\ other \in [Procs -> Procs]

(* Noncritical section: a process may stay here forever (no fairness). *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, unchecked, other >>

(* Raise own bit and prepare to check all other processes. *)
e1(self) ==
    /\ pc[self] = "e1"
    /\ x' = [x EXCEPT ![self] = TRUE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED other

(* Pick the next process to check, or enter the critical section. *)
e2(self) ==
    /\ pc[self] = "e2"
    /\ IF unchecked[self] # {}
         THEN \E i \in unchecked[self] :
                /\ other' = [other EXCEPT ![self] = i]
                /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {i}]
                /\ pc' = [pc EXCEPT ![self] = "e3"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED << unchecked, other >>
    /\ UNCHANGED x

(* Examine the bit of the chosen process. *)
e3(self) ==
    /\ pc[self] = "e3"
    /\ IF x[other[self]]
         THEN IF self > other[self]
                THEN pc' = [pc EXCEPT ![self] = "e4"]
                ELSE pc' = [pc EXCEPT ![self] = "e6"]
         ELSE pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << x, unchecked, other >>

(* Back off: lower-numbered process has priority. *)
e4(self) ==
    /\ pc[self] = "e4"
    /\ x' = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "e5"]
    /\ UNCHANGED << unchecked, other >>

(* Wait for the higher-priority process to drop its bit, then restart. *)
e5(self) ==
    /\ pc[self] = "e5"
    /\ ~x[other[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, unchecked, other >>

(* Wait for a higher-numbered process to drop its bit. *)
e6(self) ==
    /\ pc[self] = "e6"
    /\ ~x[other[self]]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED << x, unchecked, other >>

(* Critical section. *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "f"]
    /\ UNCHANGED << x, unchecked, other >>

(* Exit protocol: lower own bit. *)
f(self) ==
    /\ pc[self] = "f"
    /\ x' = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << unchecked, other >>

(* All steps of process self except leaving the noncritical section. *)
FairSteps(self) ==
    \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
    \/ e5(self) \/ e6(self) \/ cs(self) \/ f(self)

p(self) == ncs(self) \/ FairSteps(self)

Next == \E self \in Procs : p(self)

(* Weak fairness on every step except leaving the noncritical section. *)
Fairness == \A self \in Procs : WF_vars(FairSteps(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

InCS(i) == pc[i] = "cs"

(* Safety: at most one process in the critical section. *)
MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

(* Liveness: if some process is trying, some process eventually enters. *)
DeadlockFreedom ==
    (\E i \in Procs : pc[i] \in Trying) ~> (\E i \in Procs : InCS(i))

(* Liveness (expected to FAIL): every trying process eventually enters. *)
StarvationFreedom ==
    \A i \in Procs : (pc[i] \in Trying) ~> InCS(i)

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom
=============================================================================
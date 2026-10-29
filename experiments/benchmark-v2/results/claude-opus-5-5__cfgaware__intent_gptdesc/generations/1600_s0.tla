------------------------------ MODULE FastMutex ------------------------------
(***************************************************************************)
(* Lamport-style fast mutual exclusion for N processes.                    *)
(*                                                                         *)
(* Fast path: a process sets its intent flag b[self], writes x := self,    *)
(* and if y = 0 writes y := self.  If x is still self, it enters the       *)
(* critical section with no further waiting.                               *)
(*                                                                         *)
(* Slow path: if y # 0, the process withdraws its intent and waits for     *)
(* y = 0 before retrying.  If x # self after setting y, the process        *)
(* withdraws its intent and waits until no other process advertises       *)
(* intent.  If it still owns y, it enters.  Otherwise it waits for y = 0   *)
(* and retries.                                                            *)
(*                                                                         *)
(* Exit: y := 0 releases ownership, then b[self] := FALSE clears intent.   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, defaultInitValue

ASSUME N \in Nat /\ N > 1

Procs == 1..N

VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5", "l6", "l7",
           "l8", "l9", "l10", "cs", "l11", "l12"}

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ j = [i \in Procs |-> defaultInitValue]
    /\ pc = [i \in Procs |-> "ncs"]

\* Non-critical section: decide to try again
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Advertise intent
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED << x, y, j >>

\* Fast attempt: claim x
l1(self) ==
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED << y, b, j >>

\* Contention check on owner indicator y
l2(self) ==
    /\ pc[self] = "l2"
    /\ IF y # 0
          THEN pc' = [pc EXCEPT ![self] = "l3"]
          ELSE pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, y, b, j >>

\* Back off: withdraw intent
l3(self) ==
    /\ pc[self] = "l3"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "l4"]
    /\ UNCHANGED << x, y, j >>

\* Wait for owner to be released, then retry
l4(self) ==
    /\ pc[self] = "l4"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Claim ownership indicator
l5(self) ==
    /\ pc[self] = "l5"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l6"]
    /\ UNCHANGED << x, b, j >>

\* Fast-path success check
l6(self) ==
    /\ pc[self] = "l6"
    /\ IF x # self
          THEN pc' = [pc EXCEPT ![self] = "l7"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

\* Fast attempt failed: withdraw intent, begin scanning others
l7(self) ==
    /\ pc[self] = "l7"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "l8"]
    /\ UNCHANGED << x, y >>

\* Deterministic scan: wait until each process withdraws its intent
l8(self) ==
    /\ pc[self] = "l8"
    /\ IF j[self] <= N
          THEN /\ ~b[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "l8"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
               /\ j' = j
    /\ UNCHANGED << x, y, b >>

\* Slow-path decision: still owner?
l9(self) ==
    /\ pc[self] = "l9"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l10"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

\* Lost: wait for release, then retry
l10(self) ==
    /\ pc[self] = "l10"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "l11"]
    /\ UNCHANGED << x, y, b, j >>

\* Cleanup: release ownership indicator
l11(self) ==
    /\ pc[self] = "l11"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l12"]
    /\ UNCHANGED << x, b, j >>

\* Cleanup: clear advertised intent
l12(self) ==
    /\ pc[self] = "l12"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << x, y, j >>

Proc(self) ==
    \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
    \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
    \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

Next == \E self \in Procs : Proc(self)

\* Weak fairness for every individual process
Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(Proc(self))

-----------------------------------------------------------------------------
(* Auxiliary definitions and properties *)

InCS == {i \in Procs : pc[i] = "cs"}

SomeoneInCS == \E i \in Procs : pc[i] = "cs"

\* A process has detected contention and is on the slow / back-off path
Contention == \E i \in Procs : pc[i] \in {"l3", "l4", "l7", "l8", "l9", "l10"}

PossibleCounts == 0..1

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> Labels]
    /\ j \in [Procs -> (1..(N+1)) \cup {defaultInitValue}]

MutualExclusion == \A i, k \in Procs : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

\* Proper cleanup: a process outside its trying/exiting section holds no
\* intent and no ownership marker
Cleanup == \A i \in Procs : pc[i] = "ncs" => (~b[i] /\ y # i)

Invariant == /\ TypeOK
             /\ MutualExclusion
             /\ Cleanup

\* Number of processes in the critical section is always a possible count
_POSSIBLE == Cardinality(InCS) \in PossibleCounts

\* Global progress: some process enters the critical section infinitely often
\* Progress under contention: a process that detects contention eventually
\* either enters or retries
Liveness ==
    /\ []<>SomeoneInCS
    /\ \A i \in Procs :
         (pc[i] \in {"l3", "l7"}) ~> (pc[i] \in {"cs", "start"})

=============================================================================
---------------------------- MODULE DijkstraMutex ----------------------------
(***************************************************************************)
(* Dijkstra's original mutual-exclusion algorithm (CACM 1965) for an       *)
(* arbitrary finite set Proc of processes.                                 *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   b[i] : FALSE iff process i has announced it wants to enter.           *)
(*   c[i] : FALSE iff process i is in its final scan or critical section.  *)
(*   k    : the shared pointer used for arbitration.                       *)
(*                                                                         *)
(* Each process repeatedly does the following:                             *)
(*   1. It announces intent by setting b[self] to FALSE.                   *)
(*   2. While k # self, it sets c[self] to TRUE and reads k. If the        *)
(*      process that k names is not trying, it sets k to self.             *)
(*   3. It sets c[self] to FALSE and scans the other processes in an       *)
(*      arbitrary order. If some other process j has c[j] = FALSE, it      *)
(*      returns to step 2.                                                 *)
(*   4. It enters the critical section, then resets c[self] and b[self],   *)
(*      and performs noncritical work.                                     *)
(*                                                                         *)
(* Fairness is weak fairness of every step of a process except the         *)
(* noncritical-section step "ncs". A process may therefore stay forever    *)
(* in its noncritical section.                                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Proc, defaultInitValue

ASSUME Proc # {} /\ IsFiniteSet(Proc)

VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

Labels == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li3c", "Li3d",
           "Li4a", "Li4b", "cs", "Li5", "Li6", "ncs"}

TypeOK ==
  /\ b \in [Proc -> BOOLEAN]
  /\ c \in [Proc -> BOOLEAN]
  /\ k \in Proc
  /\ pc \in [Proc -> Labels]
  /\ \A i \in Proc : temp[i] \in Proc \cup SUBSET Proc \cup {defaultInitValue}

Init ==
  /\ b = [i \in Proc |-> TRUE]
  /\ c = [i \in Proc |-> TRUE]
  /\ k \in Proc
  /\ temp = [i \in Proc |-> defaultInitValue]
  /\ pc = [i \in Proc |-> "Li0"]

\* Announce intent.
Li0(self) ==
  /\ pc[self] = "Li0"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ pc' = [pc EXCEPT ![self] = "Li1"]
  /\ UNCHANGED << c, k, temp >>

\* Examine the shared pointer.
Li1(self) ==
  /\ pc[self] = "Li1"
  /\ IF k # self
       THEN pc' = [pc EXCEPT ![self] = "Li2"]
       ELSE pc' = [pc EXCEPT ![self] = "Li4a"]
  /\ UNCHANGED << b, c, k, temp >>

Li2(self) ==
  /\ pc[self] = "Li2"
  /\ c' = [c EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "Li3a"]
  /\ UNCHANGED << b, k, temp >>

\* Read the pointer.
Li3a(self) ==
  /\ pc[self] = "Li3a"
  /\ temp' = [temp EXCEPT ![self] = k]
  /\ pc' = [pc EXCEPT ![self] = "Li3b"]
  /\ UNCHANGED << b, c, k >>

\* Check whether the process the pointer names is trying.
Li3b(self) ==
  /\ pc[self] = "Li3b"
  /\ IF b[temp[self]]
       THEN pc' = [pc EXCEPT ![self] = "Li3c"]
       ELSE pc' = [pc EXCEPT ![self] = "Li3d"]
  /\ UNCHANGED << b, c, k, temp >>

\* Take the pointer.
Li3c(self) ==
  /\ pc[self] = "Li3c"
  /\ k' = self
  /\ pc' = [pc EXCEPT ![self] = "Li3d"]
  /\ UNCHANGED << b, c, temp >>

Li3d(self) ==
  /\ pc[self] = "Li3d"
  /\ pc' = [pc EXCEPT ![self] = "Li1"]
  /\ UNCHANGED << b, c, k, temp >>

\* Begin the final scan.
Li4a(self) ==
  /\ pc[self] = "Li4a"
  /\ c' = [c EXCEPT ![self] = FALSE]
  /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
  /\ pc' = [pc EXCEPT ![self] = "Li4b"]
  /\ UNCHANGED << b, k >>

\* Scan the other processes in a nondeterministic order.
Li4b(self) ==
  /\ pc[self] = "Li4b"
  /\ IF temp[self] # {}
       THEN \E j \in temp[self] :
              /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
              /\ IF ~c[j]
                   THEN pc' = [pc EXCEPT ![self] = "Li1"]
                   ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED temp
  /\ UNCHANGED << b, c, k >>

\* Critical section.
cs(self) ==
  /\ pc[self] = "cs"
  /\ TRUE
  /\ pc' = [pc EXCEPT ![self] = "Li5"]
  /\ UNCHANGED << b, c, k, temp >>

Li5(self) ==
  /\ pc[self] = "Li5"
  /\ c' = [c EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "Li6"]
  /\ UNCHANGED << b, k, temp >>

\* Reset the announcement.
Li6(self) ==
  /\ pc[self] = "Li6"
  /\ b' = [b EXCEPT ![self] = TRUE]
  /\ pc' = [pc EXCEPT ![self] = "ncs"]
  /\ UNCHANGED << c, k, temp >>

\* Noncritical section.
ncs(self) ==
  /\ pc[self] = "ncs"
  /\ TRUE
  /\ pc' = [pc EXCEPT ![self] = "Li0"]
  /\ UNCHANGED << b, c, k, temp >>

P(self) == Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
           \/ Li3c(self) \/ Li3d(self) \/ Li4a(self) \/ Li4b(self)
           \/ cs(self) \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == \E self \in Proc : P(self)

\* Weak fairness on every step except leaving the noncritical section.
Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* Safety: at most one process is in its critical section.
MutualExclusion ==
  \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* A process is trying when it is past its noncritical section and has not
\* yet left its critical section.
Trying(i) == pc[i] \notin {"Li5", "Li6", "ncs"}

\* Liveness (deadlock freedom): if some process is trying, some process
\* eventually enters its critical section.
DeadlockFreedom ==
  \A i \in Proc : Trying(i) ~> (\E j \in Proc : pc[j] = "cs")

\* Optional, stronger liveness (starvation freedom): every trying process
\* eventually enters its own critical section. Dijkstra's algorithm does NOT
\* guarantee this, so TLC can produce a counterexample when N >= 2.
StarvationFreedom ==
  \A i \in Proc : Trying(i) ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================
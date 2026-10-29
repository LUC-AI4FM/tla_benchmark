------------------------------- MODULE DijkstraMutex -------------------------------
(***************************************************************************)
(* Dijkstra's mutual exclusion algorithm from "Solution of a Problem in    *)
(* Concurrent Programming Control" (CACM, 1965).                           *)
(*                                                                         *)
(* Each process i has two shared boolean flags, b[i] and c[i], and all     *)
(* processes share an integer variable k that holds a process identifier.  *)
(*                                                                         *)
(*   Li0: b[i] := false                                                    *)
(*   Li1: if k # i then                                                    *)
(*   Li2:     c[i] := true                                                 *)
(*   Li3:     if b[k] then k := i                                          *)
(*            goto Li1                                                     *)
(*        else                                                             *)
(*   Li4:     c[i] := false                                                *)
(*            for j # i: if not c[j] then goto Li1                         *)
(*        critical section                                                 *)
(*   Li5: c[i] := true                                                     *)
(*   Li6: b[i] := true                                                     *)
(*        noncritical section (may remain there forever)                   *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Proc

ASSUME Proc # {}

VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

Labels == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b",
           "cs", "Li5", "Li6", "ncs"}

TypeOK ==
    /\ b \in [Proc -> BOOLEAN]
    /\ c \in [Proc -> BOOLEAN]
    /\ k \in Proc
    /\ pc \in [Proc -> Labels]
    /\ temp \in [Proc -> SUBSET Proc]

Init ==
    /\ b = [i \in Proc |-> TRUE]
    /\ c = [i \in Proc |-> TRUE]
    /\ k \in Proc
    /\ temp = [i \in Proc |-> {}]
    /\ pc = [i \in Proc |-> "Li0"]

\* Li0: announce intent to enter
Li0(self) ==
    /\ pc[self] = "Li0"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << c, k, temp >>

\* Li1: check whether we hold priority (k = self)
Li1(self) ==
    /\ pc[self] = "Li1"
    /\ IF k # self
         THEN pc' = [pc EXCEPT ![self] = "Li2"]
         ELSE pc' = [pc EXCEPT ![self] = "Li4a"]
    /\ UNCHANGED << b, c, k, temp >>

\* Li2: withdraw from the final contention phase
Li2(self) ==
    /\ pc[self] = "Li2"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li3a"]
    /\ UNCHANGED << b, k, temp >>

\* Li3a: test whether the current priority holder is idle
Li3a(self) ==
    /\ pc[self] = "Li3a"
    /\ IF b[k]
         THEN pc' = [pc EXCEPT ![self] = "Li3b"]
         ELSE pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << b, c, k, temp >>

\* Li3b: seize priority, then retry
Li3b(self) ==
    /\ pc[self] = "Li3b"
    /\ k' = self
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED << b, c, temp >>

\* Li4a: enter final contention phase
Li4a(self) ==
    /\ pc[self] = "Li4a"
    /\ c' = [c EXCEPT ![self] = FALSE]
    /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "Li4b"]
    /\ UNCHANGED << b, k >>

\* Li4b: check every other process, one at a time
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

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "Li5"]
    /\ UNCHANGED << b, c, k, temp >>

\* Exit protocol
Li5(self) ==
    /\ pc[self] = "Li5"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li6"]
    /\ UNCHANGED << b, k, temp >>

Li6(self) ==
    /\ pc[self] = "Li6"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << c, k, temp >>

\* Noncritical section: the process may stay here forever (no fairness)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "Li0"]
    /\ UNCHANGED << b, c, k, temp >>

P(self) ==
    \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
    \/ Li4a(self) \/ Li4b(self) \/ cs(self) \/ Li5(self) \/ Li6(self)
    \/ ncs(self)

Next == \E self \in Proc : P(self)

\* Weak fairness on every step except leaving the noncritical section
Fairness ==
    \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

\* Safety: mutual exclusion
MutualExclusion ==
    \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Trying(i) == pc[i] \in {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b"}

\* Liveness: deadlock freedom (holds under Fairness)
DeadlockFree ==
    (\E i \in Proc : Trying(i)) ~> (\E j \in Proc : pc[j] = "cs")

\* Starvation freedom: NOT guaranteed by this algorithm.
\* Checking this property with TLC (|Proc| >= 2) yields a counterexample.
StarvationFree ==
    \A i \in Proc : Trying(i) ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree
=============================================================================
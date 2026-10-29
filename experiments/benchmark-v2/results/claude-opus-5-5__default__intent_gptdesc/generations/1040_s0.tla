--------------------------- MODULE DijkstraMutex ---------------------------
(***************************************************************************)
(* Dijkstra's 1965 mutual exclusion algorithm for N processes ("Solution  *)
(* of a Problem in Concurrent Programming Control", CACM 8(9)).           *)
(*                                                                         *)
(* Shared variables:                                                       *)
(*   b[i] : FALSE means process i has left its remainder and wants the CS  *)
(*   c[i] : FALSE means process i is in its final contention phase         *)
(*   k    : the selector, the process currently favoured                   *)
(*                                                                         *)
(* Algorithm for process self (labels correspond to pc values):            *)
(*                                                                         *)
(*  Li0:  b[self] := FALSE                                                 *)
(*  Li1:  if k # self then                                                 *)
(*  Li2:     c[self] := TRUE                                               *)
(*  Li3a:    if b[k] then                                                  *)
(*  Li3b:       k := self                                                  *)
(*           goto Li1                                                      *)
(*  Li4a: c[self] := FALSE ; temp := Proc \ {self}                         *)
(*  Li4b: while temp # {} do                                               *)
(*          choose any j in temp (nondeterministic order) ;                *)
(*          temp := temp \ {j} ;                                           *)
(*          if ~c[j] then goto Li1                                         *)
(*  cs:   critical section                                                 *)
(*  Li5:  c[self] := TRUE                                                  *)
(*  Li6:  b[self] := TRUE                                                  *)
(*  ncs:  noncritical (remainder) section ; goto Li0                       *)
(*                                                                         *)
(* Each step reads or writes at most one shared variable, so the grain of *)
(* atomicity matches the original algorithm.                               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Proc            \* The finite, nonempty set of processes

ASSUME ProcAssump == Proc # {}

VARIABLES b, c, k, pc, temp

vars == <<b, c, k, pc, temp>>

Labels == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b",
           "cs", "Li5", "Li6", "ncs"}

TypeOK ==
    /\ b    \in [Proc -> BOOLEAN]
    /\ c    \in [Proc -> BOOLEAN]
    /\ k    \in Proc
    /\ pc   \in [Proc -> Labels]
    /\ temp \in [Proc -> SUBSET Proc]

(***************************************************************************)
(* Initially no process is interested: all flags are TRUE.  The selector  *)
(* may point to any process.                                               *)
(***************************************************************************)
Init ==
    /\ b    = [i \in Proc |-> TRUE]
    /\ c    = [i \in Proc |-> TRUE]
    /\ k    \in Proc
    /\ pc   = [i \in Proc |-> "Li0"]
    /\ temp = [i \in Proc |-> {}]

Li0(self) ==
    /\ pc[self] = "Li0"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED <<c, k, temp>>

Li1(self) ==
    /\ pc[self] = "Li1"
    /\ IF k # self
         THEN pc' = [pc EXCEPT ![self] = "Li2"]
         ELSE pc' = [pc EXCEPT ![self] = "Li4a"]
    /\ UNCHANGED <<b, c, k, temp>>

Li2(self) ==
    /\ pc[self] = "Li2"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li3a"]
    /\ UNCHANGED <<b, k, temp>>

Li3a(self) ==
    /\ pc[self] = "Li3a"
    /\ IF b[k]
         THEN pc' = [pc EXCEPT ![self] = "Li3b"]
         ELSE pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED <<b, c, k, temp>>

Li3b(self) ==
    /\ pc[self] = "Li3b"
    /\ k' = self
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED <<b, c, temp>>

Li4a(self) ==
    /\ pc[self] = "Li4a"
    /\ c' = [c EXCEPT ![self] = FALSE]
    /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "Li4b"]
    /\ UNCHANGED <<b, k>>

(* Other processes are examined one at a time, in an arbitrary order. *)
Li4b(self) ==
    /\ pc[self] = "Li4b"
    /\ IF temp[self] # {}
         THEN \E j \in temp[self] :
                 /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
                 /\ IF ~ c[j]
                      THEN pc' = [pc EXCEPT ![self] = "Li1"]
                      ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED temp
    /\ UNCHANGED <<b, c, k>>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "Li5"]
    /\ UNCHANGED <<b, c, k, temp>>

Li5(self) ==
    /\ pc[self] = "Li5"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li6"]
    /\ UNCHANGED <<b, k, temp>>

Li6(self) ==
    /\ pc[self] = "Li6"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<c, k, temp>>

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "Li0"]
    /\ UNCHANGED <<b, c, k, temp>>

P(self) ==
    \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
    \/ Li4a(self) \/ Li4b(self) \/ cs(self) \/ Li5(self) \/ Li6(self)
    \/ ncs(self)

Next == \E self \in Proc : P(self)

(***************************************************************************)
(* Safety-only specification: no fairness whatsoever.                      *)
(***************************************************************************)
SafetySpec == Init /\ [][Next]_vars

(***************************************************************************)
(* Weak fairness on every process step, including leaving the noncritical *)
(* section.  This is the "usual" fairness assumption, used for the weak   *)
(* form of deadlock freedom.                                               *)
(***************************************************************************)
WeakFairSpec == Init /\ [][Next]_vars /\ \A self \in Proc : WF_vars(P(self))

(***************************************************************************)
(* The intended specification: weak fairness on every step except leaving *)
(* the noncritical section, so a process may legitimately remain in ncs   *)
(* forever.  Used for the strong form of deadlock freedom.                 *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars
             /\ \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

-----------------------------------------------------------------------------
(***************************************************************************)
(*                         Safety properties                              *)
(***************************************************************************)
InCS(i) == pc[i] = "cs"

MutualExclusion == \A i, j \in Proc : (i # j) => ~ (InCS(i) /\ InCS(j))

(* Auxiliary invariants used to establish mutual exclusion.               *)
BInv == \A i \in Proc : (pc[i] \notin {"Li0", "ncs"}) => ~ b[i]

CInv == \A i \in Proc : (pc[i] \in {"Li4b", "cs", "Li5"}) => ~ c[i]

(* i "has passed j": i has already found c[j] = TRUE in its final scan.   *)
Passed(i, j) ==
    \/ pc[i] \in {"cs", "Li5"}
    \/ (pc[i] = "Li4b" /\ j \notin temp[i])

PassInv ==
    \A i, j \in Proc : (i # j) => ~ (Passed(i, j) /\ Passed(j, i))

TempInv == \A i \in Proc : (pc[i] = "Li4b") => (i \notin temp[i])

Inv == TypeOK /\ BInv /\ CInv /\ TempInv /\ PassInv

THEOREM SafetySpec => []TypeOK
THEOREM SafetySpec => []Inv
THEOREM SafetySpec => []MutualExclusion

-----------------------------------------------------------------------------
(***************************************************************************)
(*                        Liveness properties                             *)
(***************************************************************************)

(* Weak form: if some process is trying to enter (at Li0), some process   *)
(* eventually enters its critical section.                                 *)
DeadlockFree ==
    \A i \in Proc : (pc[i] = "Li0") ~> (\E j \in Proc : InCS(j))

(* Strong form: if any process is in the trying region (anywhere except   *)
(* the exit protocol Li5, Li6 and the remainder ncs), then eventually some *)
(* process enters its critical section, even though other processes may  *)
(* stay in ncs forever.                                                    *)
TryingRegion(i) == pc[i] \notin {"Li5", "Li6", "ncs"}

DeadlockFreedom ==
    \A i \in Proc : TryingRegion(i) ~> (\E j \in Proc : InCS(j))

(* Starvation freedom: every trying process eventually enters.            *)
StarvationFree ==
    \A i \in Proc : TryingRegion(i) ~> InCS(i)

THEOREM WeakFairSpec => DeadlockFree
THEOREM Spec => DeadlockFree
THEOREM Spec => DeadlockFreedom

(***************************************************************************)
(* Dijkstra's algorithm is NOT starvation free.  With two or more          *)
(* processes, TLC produces a counterexample to StarvationFree under both  *)
(* Spec and WeakFairSpec: a process i can be overtaken forever, because   *)
(* each time it reaches Li3a another process j has b[j] = FALSE and k = j, *)
(* or it finds c[j] = FALSE at Li4b, while j repeatedly enters the CS.     *)
(* The following theorem records the violation.                            *)
(***************************************************************************)
THEOREM (Proc # {} /\ \E i, j \in Proc : i # j) => ~ (Spec => StarvationFree)

=============================================================================
--------------------------- MODULE DijkstraMutex ---------------------------
(***************************************************************************)
(* Dijkstra's 1965 mutual exclusion algorithm for an arbitrary finite set  *)
(* of processes Proc.                                                      *)
(*                                                                         *)
(* Shared state:                                                           *)
(*   b[i] : Boolean flag. FALSE means process i wants to enter.            *)
(*   c[i] : Boolean flag. FALSE means process i is in the final            *)
(*          "claiming" phase.                                              *)
(*   k    : the shared arbitration pointer (a process).                    *)
(*                                                                         *)
(* Each process repeatedly does the following:                             *)
(*   Li0      : announce intent (b[i] := FALSE)                            *)
(*   Li1      : if k # i then go to Li2, else go to Li4a                   *)
(*   Li2      : c[i] := TRUE                                               *)
(*   Li3a     : read the pointer k                                         *)
(*   Li3b     : if b[k] is TRUE (owner not interested) then go to Li3c,    *)
(*              else go back to Li1                                        *)
(*   Li3c     : k := i, then go back to Li1                                *)
(*   Li4a     : c[i] := FALSE, then prepare to scan the others             *)
(*   Li4b     : scan the other processes in arbitrary order; if some       *)
(*              c[j] = FALSE then go back to Li1                           *)
(*   cs       : critical section                                           *)
(*   Li5      : c[i] := TRUE                                               *)
(*   Li6      : b[i] := TRUE (reset the announcement)                      *)
(*   ncs      : noncritical section (may remain there forever)             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Proc

ASSUME Proc # {} /\ IsFiniteSet(Proc)

VARIABLES
    b,          \* b[i] : announcement flag of process i
    c,          \* c[i] : claim flag of process i
    k,          \* shared arbitration pointer
    tk,         \* tk[i] : local copy of k read by process i
    unchecked,  \* unchecked[i] : processes i still has to examine in Li4b
    pc          \* pc[i] : control point of process i

vars == <<b, c, k, tk, unchecked, pc>>

Labels == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li3c",
           "Li4a", "Li4b", "cs", "Li5", "Li6", "ncs"}

TypeOK ==
    /\ b \in [Proc -> BOOLEAN]
    /\ c \in [Proc -> BOOLEAN]
    /\ k \in Proc
    /\ tk \in [Proc -> Proc]
    /\ unchecked \in [Proc -> SUBSET Proc]
    /\ pc \in [Proc -> Labels]

Init ==
    /\ b = [i \in Proc |-> TRUE]
    /\ c = [i \in Proc |-> TRUE]
    /\ k \in Proc
    /\ tk \in [Proc -> Proc]
    /\ unchecked = [i \in Proc |-> {}]
    /\ pc = [i \in Proc |-> "Li0"]

-----------------------------------------------------------------------------
(* Process actions *)

Li0(self) ==
    /\ pc[self] = "Li0"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED <<c, k, tk, unchecked>>

Li1(self) ==
    /\ pc[self] = "Li1"
    /\ IF k # self
          THEN pc' = [pc EXCEPT ![self] = "Li2"]
          ELSE pc' = [pc EXCEPT ![self] = "Li4a"]
    /\ UNCHANGED <<b, c, k, tk, unchecked>>

Li2(self) ==
    /\ pc[self] = "Li2"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li3a"]
    /\ UNCHANGED <<b, k, tk, unchecked>>

Li3a(self) ==
    /\ pc[self] = "Li3a"
    /\ tk' = [tk EXCEPT ![self] = k]
    /\ pc' = [pc EXCEPT ![self] = "Li3b"]
    /\ UNCHANGED <<b, c, k, unchecked>>

Li3b(self) ==
    /\ pc[self] = "Li3b"
    /\ IF b[tk[self]]
          THEN pc' = [pc EXCEPT ![self] = "Li3c"]
          ELSE pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED <<b, c, k, tk, unchecked>>

Li3c(self) ==
    /\ pc[self] = "Li3c"
    /\ k' = self
    /\ pc' = [pc EXCEPT ![self] = "Li1"]
    /\ UNCHANGED <<b, c, tk, unchecked>>

Li4a(self) ==
    /\ pc[self] = "Li4a"
    /\ c' = [c EXCEPT ![self] = FALSE]
    /\ unchecked' = [unchecked EXCEPT ![self] = Proc \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "Li4b"]
    /\ UNCHANGED <<b, k, tk>>

\* Examine the remaining processes one at a time, in nondeterministic order.
Li4b(self) ==
    /\ pc[self] = "Li4b"
    /\ IF unchecked[self] # {}
          THEN \E j \in unchecked[self] :
                  /\ unchecked' = [unchecked EXCEPT ![self] = @ \ {j}]
                  /\ IF ~c[j]
                        THEN pc' = [pc EXCEPT ![self] = "Li1"]
                        ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED unchecked
    /\ UNCHANGED <<b, c, k, tk>>

CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "Li5"]
    /\ UNCHANGED <<b, c, k, tk, unchecked>>

Li5(self) ==
    /\ pc[self] = "Li5"
    /\ c' = [c EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "Li6"]
    /\ UNCHANGED <<b, k, tk, unchecked>>

Li6(self) ==
    /\ pc[self] = "Li6"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<c, k, tk, unchecked>>

\* Noncritical section: no fairness, so a process may stay here forever.
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "Li0"]
    /\ UNCHANGED <<b, c, k, tk, unchecked>>

\* All steps of a process except the noncritical-section step.
Trying(self) ==
    \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
    \/ Li3c(self) \/ Li4a(self) \/ Li4b(self) \/ CS(self)
    \/ Li5(self) \/ Li6(self)

P(self) == Trying(self) \/ NCS(self)

Next == \E self \in Proc : P(self)

\* Weak fairness on every step except the noncritical section.
Fairness == \A self \in Proc : WF_vars(Trying(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

\* Safety: mutual exclusion.
MutualExclusion ==
    \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: deadlock freedom. If some process is trying to enter
\* (it is past the noncritical section and not in its exit protocol),
\* then eventually some process is in its critical section.
DeadlockFree ==
    (\E i \in Proc : pc[i] \notin {"Li5", "Li6", "ncs"})
        ~> (\E i \in Proc : pc[i] = "cs")

\* Optional, stronger liveness: starvation freedom. Every process that is
\* trying eventually enters its own critical section. Dijkstra's algorithm
\* does NOT guarantee this; model checking with |Proc| >= 2 is expected to
\* produce a counterexample in which one process is overtaken forever.
StarvationFree ==
    \A i \in Proc :
        (pc[i] \notin {"Li5", "Li6", "ncs"}) ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree
=============================================================================
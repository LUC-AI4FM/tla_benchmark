---------------------------- MODULE DijkstraMutex ----------------------------
(***************************************************************************)
(* Dijkstra's original mutual-exclusion algorithm for an arbitrary finite  *)
(* set Proc of processes.  Shared variables:                               *)
(*   b[i] : FALSE means process i is interested in entering.               *)
(*   c[i] : FALSE means process i is in its final contention phase.        *)
(*   k    : the selector, suggesting which process to favour.              *)
(* Initially every flag is TRUE (no interest).                             *)
(* In label Li4b a process checks the other processes' c flags in an       *)
(* arbitrary, nondeterministically chosen order.                           *)
(***************************************************************************)

CONSTANT Proc, defaultInitValue

ASSUME Proc # {}

VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

ProcSet == Proc

Init == /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        /\ temp = [self \in Proc |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Li0"]

Li0(self) == /\ pc[self] = "Li0"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Li1"]
             /\ UNCHANGED << c, k, temp >>

Li1(self) == /\ pc[self] = "Li1"
             /\ IF k # self
                   THEN pc' = [pc EXCEPT ![self] = "Li2"]
                   ELSE pc' = [pc EXCEPT ![self] = "Li4a"]
             /\ UNCHANGED << b, c, k, temp >>

Li2(self) == /\ pc[self] = "Li2"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li3a"]
             /\ UNCHANGED << b, k, temp >>

Li3a(self) == /\ pc[self] = "Li3a"
              /\ temp' = [temp EXCEPT ![self] = k]
              /\ pc' = [pc EXCEPT ![self] = "Li3b"]
              /\ UNCHANGED << b, c, k >>

Li3b(self) == /\ pc[self] = "Li3b"
              /\ IF b[temp[self]]
                    THEN pc' = [pc EXCEPT ![self] = "Li3c"]
                    ELSE pc' = [pc EXCEPT ![self] = "Li3d"]
              /\ UNCHANGED << b, c, k, temp >>

Li3c(self) == /\ pc[self] = "Li3c"
              /\ k' = self
              /\ pc' = [pc EXCEPT ![self] = "Li3d"]
              /\ UNCHANGED << b, c, temp >>

Li3d(self) == /\ pc[self] = "Li3d"
              /\ pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, k, temp >>

Li4a(self) == /\ pc[self] = "Li4a"
              /\ c' = [c EXCEPT ![self] = FALSE]
              /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
              /\ pc' = [pc EXCEPT ![self] = "Li4b"]
              /\ UNCHANGED << b, k >>

Li4b(self) == /\ pc[self] = "Li4b"
              /\ IF temp[self] # {}
                    THEN /\ \E j \in temp[self] :
                              /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
                              /\ IF ~ c[j]
                                    THEN pc' = [pc EXCEPT ![self] = "Li1"]
                                    ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                         /\ temp' = temp
              /\ UNCHANGED << b, c, k >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE  \* the critical section
            /\ pc' = [pc EXCEPT ![self] = "Li5"]
            /\ UNCHANGED << b, c, k, temp >>

Li5(self) == /\ pc[self] = "Li5"
             /\ c' = [c EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "Li6"]
             /\ UNCHANGED << b, k, temp >>

Li6(self) == /\ pc[self] = "Li6"
             /\ b' = [b EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << c, k, temp >>

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE  \* non-critical remainder
             /\ pc' = [pc EXCEPT ![self] = "Li0"]
             /\ UNCHANGED << b, c, k, temp >>

P(self) == \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self)
           \/ Li3b(self) \/ Li3c(self) \/ Li3d(self) \/ Li4a(self)
           \/ Li4b(self) \/ cs(self) \/ Li5(self) \/ Li6(self)
           \/ ncs(self)

Next == \E self \in Proc : P(self)

(***************************************************************************)
(* Spec: weak fairness on every process (weak form of deadlock freedom).   *)
(***************************************************************************)
Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars(P(self))

(***************************************************************************)
(* LSpec: processes may remain forever in the non-critical section, so    *)
(* fairness is required only for steps taken outside of ncs.               *)
(***************************************************************************)
LSpec == /\ Init /\ [][Next]_vars
         /\ \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

-----------------------------------------------------------------------------
TypeOK == /\ b \in [Proc -> BOOLEAN]
          /\ c \in [Proc -> BOOLEAN]
          /\ k \in Proc
          /\ pc \in [Proc -> {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li3c",
                              "Li3d", "Li4a", "Li4b", "cs", "Li5", "Li6",
                              "ncs"}]

MutualExclusion == \A i, j \in Proc :
                      (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

InTrying(i) == pc[i] \notin {"Li5", "Li6", "ncs"}

(* Weak form: a process that has begun trying leads to some process in cs *)
WeakDeadlockFreedom ==
    (\E i \in Proc : pc[i] \in {"Li1", "Li2", "Li3a", "Li3b", "Li3c",
                                "Li3d", "Li4a", "Li4b"})
       ~> (\E j \in Proc : pc[j] = "cs")

(* Strong form, checked under LSpec *)
DeadlockFreedom ==
    \A i \in Proc : InTrying(i) ~> (\E j \in Proc : pc[j] = "cs")

(* Starvation freedom: violated by this algorithm (TLC finds a           *)
(* counterexample in which one process is repeatedly overtaken).          *)
StarvationFreedom ==
    \A i \in Proc : InTrying(i) ~> (pc[i] = "cs")

THEOREM Spec => []MutualExclusion
THEOREM LSpec => []MutualExclusion
THEOREM LSpec => DeadlockFreedom
=============================================================================
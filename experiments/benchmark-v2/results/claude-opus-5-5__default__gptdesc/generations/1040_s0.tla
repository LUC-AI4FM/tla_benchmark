-------------------------- MODULE DijkstraMutex --------------------------
(***************************************************************************)
(* Dijkstra's first published mutual exclusion algorithm, from:           *)
(*                                                                         *)
(*   E. W. Dijkstra, "Solution of a Problem in Concurrent Programming     *)
(*   Control", Communications of the ACM 8, 9 (September 1965), page 569. *)
(*                                                                         *)
(* A set Proc of processes (with arbitrary names) each cycle forever      *)
(* through a noncritical section and a critical section. The shared      *)
(* variables are the arrays b and c, indexed by process, and the integer *)
(* k, which here ranges over Proc instead of 1..N. In Dijkstra's paper    *)
(* the processes are numbered 1..N. The algorithm does not depend on      *)
(* that, so here they may have any names.                                 *)
(*                                                                         *)
(* Each label marks one atomic step. Dijkstra assumed only that a single *)
(* read or a single write of a shared variable is atomic. The program is *)
(* therefore split into steps that each perform at most one such access *)
(* (or one read together with a write to a local variable). The         *)
(* statement "if b[k] then k := i" is split into three steps: Li3a reads *)
(* k, Li3b reads b[k], and Li3c writes k. The loop that tests every c[j] *)
(* is split so that each iteration reads one c[j] in a single step.      *)
(*                                                                         *)
(* PlusCal version of the algorithm:                                      *)
(*                                                                         *)
(* --algorithm Mutex                                                       *)
(* { variables b = [i \in Proc |-> TRUE], c = [i \in Proc |-> TRUE],      *)
(*             k \in Proc;                                                 *)
(*   process (P \in Proc)                                                  *)
(*     variable temp = {} ;                                                *)
(*   { Li0: while (TRUE)                                                   *)
(*          {      b[self] := FALSE;                                       *)
(*            Li1: if (k # self)                                           *)
(*                   { Li2:  c[self] := TRUE;                              *)
(*                     Li3a: temp := k;                                    *)
(*                     Li3b: if (b[temp]) { Li3c: k := self };             *)
(*                           goto Li1                                      *)
(*                   };                                                    *)
(*            Li4a: c[self] := FALSE;                                      *)
(*                  temp := Proc \ {self};                                 *)
(*            Li4b: while (temp # {})                                      *)
(*                    { with (j \in temp)                                  *)
(*                        { temp := temp \ {j};                            *)
(*                          if (~c[j]) { goto Li1 }                        *)
(*                        }                                                *)
(*                    };                                                   *)
(*            cs:   skip;   \* the critical section                       *)
(*            Li5:  c[self] := TRUE;                                       *)
(*            Li6:  b[self] := TRUE;                                       *)
(*            ncs:  skip    \* the noncritical section                    *)
(*          }                                                              *)
(*   }                                                                     *)
(* }                                                                       *)
(*                                                                         *)
(* The TLA+ translation follows.                                          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Proc

ASSUME Proc # {}

VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

ProcSet == Proc

Labels == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li3c",
           "Li4a", "Li4b", "cs", "Li5", "Li6", "ncs"}

Init == /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        /\ temp = [self \in Proc |-> {}]
        /\ pc = [self \in Proc |-> "Li0"]

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
                   ELSE pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, k, temp >>

Li3c(self) == /\ pc[self] = "Li3c"
              /\ k' = self
              /\ pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, temp >>

Li4a(self) == /\ pc[self] = "Li4a"
              /\ c' = [c EXCEPT ![self] = FALSE]
              /\ temp' = [temp EXCEPT ![self] = Proc \ {self}]
              /\ pc' = [pc EXCEPT ![self] = "Li4b"]
              /\ UNCHANGED << b, k >>

Li4b(self) == /\ pc[self] = "Li4b"
              /\ IF temp[self] # {}
                   THEN \E j \in temp[self] :
                          /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
                          /\ IF ~c[j]
                               THEN pc' = [pc EXCEPT ![self] = "Li1"]
                               ELSE pc' = [pc EXCEPT ![self] = "Li4b"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                        /\ temp' = temp
              /\ UNCHANGED << b, c, k >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
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
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Li0"]
             /\ UNCHANGED << b, c, k, temp >>

P(self) == Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self)
              \/ Li3b(self) \/ Li3c(self) \/ Li4a(self) \/ Li4b(self)
              \/ cs(self) \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == \E self \in Proc : P(self)

(***************************************************************************)
(* Fairness. A process must be allowed to stay in its noncritical section *)
(* forever. So we do not want weak fairness on the whole P(self) action, *)
(* because that would force every process to leave its noncritical      *)
(* section. Instead we assert weak fairness of every step of a process   *)
(* except the ncs step. That means a process that has left its            *)
(* noncritical section keeps taking steps, which is the assumption that  *)
(* Dijkstra made.                                                         *)
(***************************************************************************)
Fairness == \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Type invariant.                                                         *)
(***************************************************************************)
TypeOK == /\ b \in [Proc -> BOOLEAN]
          /\ c \in [Proc -> BOOLEAN]
          /\ k \in Proc
          /\ pc \in [Proc -> Labels]
          /\ \A i \in Proc : temp[i] \in (SUBSET Proc) \cup Proc

(***************************************************************************)
(* Safety: mutual exclusion. No two different processes are in their     *)
(* critical sections at the same time.                                   *)
(***************************************************************************)
InCS(i) == pc[i] = "cs"

MutualExclusion == \A i, j \in Proc : (i # j) => ~(InCS(i) /\ InCS(j))

(***************************************************************************)
(* Liveness: deadlock freedom (the progress property Dijkstra required). *)
(* If some process is trying to enter its critical section, then some    *)
(* process (not necessarily the same one) eventually enters its critical *)
(* section. This holds under the fairness condition above.               *)
(***************************************************************************)
Trying(i) == pc[i] \in {"Li1", "Li2", "Li3a", "Li3b", "Li3c", "Li4a", "Li4b"}

DeadlockFree == (\E i \in Proc : Trying(i)) ~> (\E i \in Proc : InCS(i))

(***************************************************************************)
(* Starvation freedom says that every process that tries to enter its     *)
(* critical section eventually does. Dijkstra's algorithm does NOT        *)
(* satisfy this property. One process can be overtaken by other           *)
(* processes forever, even with fairness. A model checker will report a  *)
(* counterexample when there are at least two processes. We state the    *)
(* property only for that reason. Do not include it among the properties *)
(* that the spec is expected to satisfy.                                  *)
(***************************************************************************)
StarvationFree == \A i \in Proc : Trying(i) ~> InCS(i)

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree
=============================================================================
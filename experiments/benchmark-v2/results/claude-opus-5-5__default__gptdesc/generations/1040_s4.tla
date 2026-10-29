------------------------------ MODULE DijkstraMutex ------------------------------
(***************************************************************************)
(* Dijkstra's first published mutual exclusion algorithm, from:            *)
(*                                                                         *)
(*   E. W. Dijkstra, "Solution of a Problem in Concurrent Programming      *)
(*   Control", Communications of the ACM 8, 9 (September 1965), page 569.  *)
(*                                                                         *)
(* Processes are named by the elements of the constant set Proc. The      *)
(* names can be arbitrary values, not just numbers. The shared variables  *)
(* are                                                                     *)
(*                                                                         *)
(*   b : Proc -> BOOLEAN, initially all TRUE                               *)
(*   c : Proc -> BOOLEAN, initially all TRUE                               *)
(*   k \in Proc, initially arbitrary                                       *)
(*                                                                         *)
(* Each process has a local variable temp.                                 *)
(*                                                                         *)
(* Statements in Dijkstra's paper are split into separate atomic steps so *)
(* that each step reads or writes at most one shared variable entry.       *)
(* The test "for all j # i : c[j]" at Li4 is not atomic. It is modeled as *)
(* a loop that examines the c[j] one at a time, in arbitrary order. If any *)
(* c[j] is FALSE, the process returns to Li1.                              *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Proc

ASSUME Proc # {}

(***************************************************************************
--algorithm Mutex
{ variables b = [i \in Proc |-> TRUE], c = [i \in Proc |-> TRUE], k \in Proc;
  process (P \in Proc)
    variable temp ;
    { Li0: while (TRUE)
            { b[self] := FALSE;
         Li1: if (k # self) { Li2: c[self] := TRUE;
                              Li3a: temp := k;
                              Li3b: if (b[temp]) { Li3c: k := self } ;
                              Li3d: goto Li1
                            };
         Li4a: c[self] := FALSE;
               temp := Proc \ {self};
         Li4b: while (temp # {})
                { with (j \in temp)
                    { temp := temp \ {j};
                      if (~c[j]) { goto Li1 }
                    }
                };
          cs: skip;  \* the critical section
         Li5: c[self] := TRUE;
         Li6: b[self] := TRUE;
         ncs: skip   \* the noncritical section
            }
    }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue

VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        (* Process P *)
        /\ temp = [self \in Proc |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Li0"]

Li0(self) == /\ pc[self] = "Li0"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Li1"]
             /\ UNCHANGED << c, k, temp >>

Li1(self) == /\ pc[self] = "Li1"
             /\ IF k # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "Li2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Li4a"]
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
                    THEN /\ pc' = [pc EXCEPT ![self] = "Li3c"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Li3d"]
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
                    THEN /\ \E j \in temp[self]:
                              /\ temp' = [temp EXCEPT ![self] = temp[self] \ {j}]
                              /\ IF ~c[j]
                                    THEN /\ pc' = [pc EXCEPT ![self] = "Li1"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "Li4b"]
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

P(self) == Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
              \/ Li3c(self) \/ Li3d(self) \/ Li4a(self) \/ Li4b(self)
              \/ cs(self) \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == (\E self \in Proc: P(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK == /\ b \in [Proc -> BOOLEAN]
          /\ c \in [Proc -> BOOLEAN]
          /\ k \in Proc
          /\ pc \in [Proc -> {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li3c",
                              "Li3d", "Li4a", "Li4b", "cs", "Li5", "Li6",
                              "ncs"}]
          /\ \A i \in Proc :
                pc[i] \in {"Li3b", "Li3c"} => temp[i] \in Proc

(***************************************************************************)
(* Mutual exclusion: no two distinct processes are in their critical      *)
(* sections at the same time.                                              *)
(***************************************************************************)
MutualExclusion == \A i, j \in Proc :
                      (i # j) => ~ /\ pc[i] = "cs"
                                   /\ pc[j] = "cs"

(***************************************************************************)
(* Fairness. A process must be allowed to remain forever in its           *)
(* noncritical section, so we assert weak fairness of every step of a     *)
(* process except the step that leaves the noncritical section.            *)
(***************************************************************************)
LSpec == Spec /\ \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

(***************************************************************************)
(* Deadlock freedom: if some process is trying to enter its critical      *)
(* section, then some process eventually enters its critical section.     *)
(* This holds for LSpec.                                                   *)
(***************************************************************************)
Trying(i) == pc[i] \in {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li3c", "Li3d",
                        "Li4a", "Li4b"}

DeadlockFree == \A i \in Proc :
                   Trying(i) ~> (\E j \in Proc : pc[j] = "cs")

(***************************************************************************)
(* Starvation freedom: every process that tries to enter its critical     *)
(* section eventually does so. Dijkstra's algorithm does NOT satisfy this *)
(* property (even under LSpec): a process can loop forever at Li1-Li4b    *)
(* while others repeatedly enter their critical sections.                  *)
(***************************************************************************)
StarvationFree == \A i \in Proc :
                     Trying(i) ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM LSpec => DeadlockFree
=============================================================================
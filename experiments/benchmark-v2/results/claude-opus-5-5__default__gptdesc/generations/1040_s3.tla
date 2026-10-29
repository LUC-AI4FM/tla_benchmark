--------------------------- MODULE DijkstraMutex ---------------------------
(***************************************************************************)
(* Dijkstra's first published mutual exclusion algorithm, from:           *)
(*                                                                         *)
(*   E. W. Dijkstra, "Solution of a Problem in Concurrent Programming     *)
(*   Control", Communications of the ACM 8, 9 (September 1965), page 569. *)
(*                                                                         *)
(* The processes are the elements of the set Proc. Their names can be     *)
(* arbitrary. Dijkstra's processes were numbered 1..N, but the algorithm  *)
(* never uses arithmetic on process names, so any set of names works.     *)
(*                                                                         *)
(* Shared variables (as in Dijkstra's paper):                              *)
(*   b[i] : FALSE iff process i is trying to enter or is in its critical  *)
(*          section.                                                       *)
(*   c[i] : FALSE iff process i believes it has the "turn" and is checking *)
(*          that no other process does too.                                *)
(*   k    : the process that currently has priority.                       *)
(*                                                                         *)
(* Each label marks one atomic step. Dijkstra's statement                  *)
(* "if b[k] then k := i" is split into two steps, Li3a and Li3b. The read  *)
(* of b[k] and the write of k are therefore not atomic. The loop in which  *)
(* process i examines c[j] for every j # i is also broken into separate    *)
(* atomic steps, one read per step, using the process-local variable temp. *)
(*                                                                         *)
(* PlusCal version:                                                        *)
(*                                                                         *)
(* --algorithm Mutex                                                       *)
(* { variables b = [i \in Proc |-> TRUE], c = [i \in Proc |-> TRUE],       *)
(*             k \in Proc;                                                 *)
(*   fair process (P \in Proc)                                             *)
(*     variable temp = {};                                                 *)
(*   { Li0: while (TRUE)                                                   *)
(*          {  b[self] := FALSE;                                           *)
(*        Li1: if (k # self)                                               *)
(*               { Li2: c[self] := TRUE;                                   *)
(*                 Li3a: if (b[k]) { Li3b: k := self };                    *)
(*                 goto Li1                                                *)
(*               };                                                        *)
(*        Li4a: c[self] := FALSE;                                          *)
(*              temp := Proc \ {self};                                     *)
(*        Li4b: while (temp # {})                                          *)
(*               { with (j \in temp)                                       *)
(*                   { temp := temp \ {j};                                 *)
(*                     if (~c[j]) { goto Li1 }                             *)
(*                   }                                                     *)
(*               };                                                        *)
(*        cs:   skip;   \* the critical section                            *)
(*        Li5:  c[self] := TRUE;                                           *)
(*        Li6:  b[self] := TRUE;                                           *)
(*        ncs:- skip    \* the noncritical section                         *)
(*          }                                                              *)
(*   }                                                                     *)
(* }                                                                       *)
(*                                                                         *)
(* The process is "fair", but the ncs step is labeled with "-". So it is   *)
(* not fair: a process may remain in its noncritical section forever, as  *)
(* the mutual exclusion problem requires.                                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Proc

ASSUME Proc # {}

(***************************************************************************)
(*                         BEGIN TRANSLATION                               *)
(***************************************************************************)
VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

ProcSet == Proc

Init == /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        /\ temp = [self \in Proc |-> {}]
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
              /\ IF b[k]
                   THEN pc' = [pc EXCEPT ![self] = "Li3b"]
                   ELSE pc' = [pc EXCEPT ![self] = "Li1"]
              /\ UNCHANGED << b, c, k, temp >>

Li3b(self) == /\ pc[self] = "Li3b"
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
                          /\ IF ~ c[j]
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

P(self) == \/ Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self)
           \/ Li3b(self) \/ Li4a(self) \/ Li4b(self) \/ cs(self)
           \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == \E self \in Proc : P(self)

(***************************************************************************)
(* Fairness: each process is weakly fair for every step except the ncs    *)
(* step. A process may stay in its noncritical section forever, but once  *)
(* it leaves, it cannot stop forever at any other control point while it  *)
(* is able to take a step.                                                 *)
(***************************************************************************)
Fairness == \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ Fairness
(***************************************************************************)
(*                          END TRANSLATION                                *)
(***************************************************************************)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness                                                        *)
(***************************************************************************)
TypeOK == /\ b \in [Proc -> BOOLEAN]
          /\ c \in [Proc -> BOOLEAN]
          /\ k \in Proc
          /\ temp \in [Proc -> SUBSET Proc]
          /\ pc \in [Proc -> {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a",
                              "Li4b", "cs", "Li5", "Li6", "ncs"}]

(***************************************************************************)
(* Safety: mutual exclusion. No two different processes are in their      *)
(* critical sections at the same time.                                     *)
(***************************************************************************)
MutualExclusion == \A i, j \in Proc :
                      (i # j) => ~ /\ pc[i] = "cs"
                                   /\ pc[j] = "cs"

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: deadlock freedom. If some process is trying to enter its     *)
(* critical section, then eventually some process (not necessarily the    *)
(* same one) enters its critical section. A process is "trying" when it   *)
(* is not in its noncritical section and not in its exit code (Li5, Li6).  *)
(* Under weak fairness, Dijkstra's algorithm satisfies this property.     *)
(***************************************************************************)
Trying(i) == pc[i] \in {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b"}

DeadlockFree == (\E i \in Proc : Trying(i)) ~> (\E j \in Proc : pc[j] = "cs")

(***************************************************************************)
(* Starvation freedom says that every process that tries to enter its     *)
(* critical section eventually enters it. Dijkstra's algorithm does NOT   *)
(* satisfy this property. A process can loop forever through              *)
(* Li1 -> Li2 -> Li3a -> Li1 while other processes keep entering their     *)
(* critical sections. The property is included so that model checking can *)
(* show it is violated. Do not expect TLC to verify it.                    *)
(***************************************************************************)
StarvationFree == \A i \in Proc : Trying(i) ~> (pc[i] = "cs")

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree
=============================================================================
------------------------------ MODULE DijkstraMutex ------------------------------
(***************************************************************************)
(* Dijkstra's first published mutual exclusion algorithm, from:            *)
(*                                                                         *)
(*    E. W. Dijkstra, "Solution of a Problem in Concurrent Programming     *)
(*    Control", Communications of the ACM 8, 9 (September 1965), p. 569.   *)
(*                                                                         *)
(* The processes are the elements of an arbitrary set Proc.  Dijkstra     *)
(* numbered them 1..N, but the algorithm never relies on the numbering.   *)
(* Each process repeatedly runs its noncritical section and then its      *)
(* critical section.  It uses the shared variables b, c and k.  In the    *)
(* paper, b and c are Boolean arrays and k is an integer in 1..N.  Here   *)
(* they are functions with domain Proc, and k is an element of Proc.      *)
(*                                                                         *)
(* The algorithm satisfies mutual exclusion.  Under weak fairness of each *)
(* process's steps outside its noncritical section, it is deadlock free.  *)
(* It is NOT starvation free: one process can be kept out of its critical *)
(* section forever while other processes keep entering theirs.            *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Proc   \* The set of processes.  Any set of names will do.

ASSUME Proc # {}

(***************************************************************************
--algorithm Mutex
 { variables b = [i \in Proc |-> TRUE],
             c = [i \in Proc |-> TRUE],
             k \in Proc ;

   process (P \in Proc)
     variable temp = {} ;
   { Li0:  while (TRUE)
             { b[self] := FALSE ;
       Li1:    if (k # self)
                 { c[self] := TRUE ;
       Li2:        if (b[k]) { k := self } ;
                   goto Li1
                 } ;
       Li4a:   c[self] := FALSE ;
               temp := Proc \ {self} ;
       Li4b:   while (temp # {})
                 { with (j \in temp)
                     { temp := temp \ {j} ;
                       if (~c[j]) { goto Li1 }
                     }
                 } ;
       cs:     skip ;              \* the critical section
       Li5:    c[self] := TRUE ;
       Li6:    b[self] := TRUE ;
       ncs:    skip                \* the noncritical section
             }
   }
 }
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES b, c, k, pc, temp

vars == << b, c, k, pc, temp >>

ProcSet == Proc

Init == (* Global variables *)
        /\ b = [i \in Proc |-> TRUE]
        /\ c = [i \in Proc |-> TRUE]
        /\ k \in Proc
        (* Process P *)
        /\ temp = [self \in Proc |-> {}]
        /\ pc = [self \in ProcSet |-> "Li0"]

Li0(self) == /\ pc[self] = "Li0"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Li1"]
             /\ UNCHANGED << c, k, temp >>

Li1(self) == /\ pc[self] = "Li1"
             /\ IF k # self
                  THEN /\ c' = [c EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "Li2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Li4a"]
                       /\ c' = c
             /\ UNCHANGED << b, k, temp >>

Li2(self) == /\ pc[self] = "Li2"
             /\ IF b[k]
                  THEN k' = self
                  ELSE k' = k
             /\ pc' = [pc EXCEPT ![self] = "Li1"]
             /\ UNCHANGED << b, c, temp >>

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

P(self) == Li0(self) \/ Li1(self) \/ Li2(self) \/ Li4a(self) \/ Li4b(self)
              \/ cs(self) \/ Li5(self) \/ Li6(self) \/ ncs(self)

Next == (\E self \in Proc: P(self))

(***************************************************************************)
(* A process may stay in its noncritical section forever, so we assert    *)
(* weak fairness only for steps taken outside the noncritical section.    *)
(* (Asserting WF_vars(P(self)) would wrongly force every process to       *)
(* leave its noncritical section.)                                         *)
(***************************************************************************)
Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars((pc[self] # "ncs") /\ P(self))

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
Labels == {"Li0", "Li1", "Li2", "Li4a", "Li4b", "cs", "Li5", "Li6", "ncs"}

TypeOK == /\ b \in [Proc -> BOOLEAN]
          /\ c \in [Proc -> BOOLEAN]
          /\ k \in Proc
          /\ pc \in [Proc -> Labels]
          /\ temp \in [Proc -> SUBSET Proc]

(***************************************************************************)
(* Safety: mutual exclusion.  No two distinct processes are in their      *)
(* critical sections at the same time.                                    *)
(***************************************************************************)
MutualExclusion == \A i, j \in Proc :
                      (i # j) => ~ /\ pc[i] = "cs"
                                   /\ pc[j] = "cs"

(***************************************************************************)
(* Liveness: deadlock freedom.  If some process is trying to enter its    *)
(* critical section, then some process (not necessarily the same one)     *)
(* eventually enters its critical section.  The "trying" section consists *)
(* of the statements from Li0 through Li4b.                               *)
(***************************************************************************)
Trying(i) == pc[i] \in {"Li0", "Li1", "Li2", "Li4a", "Li4b"}

DeadlockFreedom ==
    (\E i \in Proc : Trying(i)) ~> (\E j \in Proc : pc[j] = "cs")

(***************************************************************************)
(* Starvation freedom: every process that tries to enter its critical     *)
(* section eventually enters it.  Dijkstra's algorithm does NOT satisfy    *)
(* this property.  A model checker finds a counterexample in which one    *)
(* process waits forever while others keep entering their critical        *)
(* sections.  It is included for exploration, not as a checked property. *)
(***************************************************************************)
StarvationFree == \A i \in Proc : Trying(i) ~> (pc[i] = "cs")

(***************************************************************************)
(* Theorems asserted by the specification.                                 *)
(***************************************************************************)
THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom
=============================================================================
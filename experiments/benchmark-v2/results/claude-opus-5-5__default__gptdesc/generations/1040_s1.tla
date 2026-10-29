--------------------------- MODULE DijkstraMutex ---------------------------
(***************************************************************************)
(* Dijkstra's first published mutual exclusion algorithm (CACM, 1965).    *)
(* A set Proc of processes cycle through a noncritical section and a      *)
(* critical section.  They communicate through the shared variables b, c *)
(* and k.  Process names are arbitrary: Proc may be any set.               *)
(*                                                                         *)
(* --algorithm Mutex                                                       *)
(*  { variables b = [i \in Proc |-> TRUE],                                 *)
(*              c = [i \in Proc |-> TRUE],                                 *)
(*              k \in Proc ;                                               *)
(*    fair process (P \in Proc)                                            *)
(*      variable temp = {} ;                                               *)
(*      { Li0:  while (TRUE)                                               *)
(*               { b[self] := FALSE ;                                      *)
(*          Li1:   if (k # self) { Li2:  c[self] := TRUE ;                 *)
(*                                 Li3a: if (b[k]) { Li3b: k := self } ;   *)
(*                                       goto Li1                          *)
(*                               } ;                                       *)
(*          Li4a:  c[self] := FALSE ;                                      *)
(*                 temp := Proc \ {self} ;                                 *)
(*          Li4b:  while (temp # {})                                       *)
(*                  { with (j \in temp)                                    *)
(*                      { temp := temp \ {j} ;                             *)
(*                        if (~c[j]) { goto Li1 }                          *)
(*                      }                                                  *)
(*                  } ;                                                    *)
(*          cs:    skip ;   \* the critical section                        *)
(*          Li5:   c[self] := TRUE ;                                       *)
(*          Li6:   b[self] := TRUE ;                                       *)
(*          ncs:   skip     \* the noncritical section                     *)
(*               }                                                         *)
(*      }                                                                  *)
(*  }                                                                      *)
(*                                                                         *)
(* The array b[i] = FALSE indicates process i wants to enter; c[i] = FALSE *)
(* indicates it is trying to claim the critical section; k is the process  *)
(* currently favored.  The steps that test Proc elements one at a time    *)
(* (Li4b) model the fact that in Dijkstra's algorithm each read of a      *)
(* shared variable is a separate atomic action.                           *)
(***************************************************************************)
EXTENDS Integers

CONSTANT Proc

ASSUME Proc # {}

(*************************** BEGIN TRANSLATION *****************************)
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

P(self) == Li0(self) \/ Li1(self) \/ Li2(self) \/ Li3a(self) \/ Li3b(self)
              \/ Li4a(self) \/ Li4b(self) \/ cs(self) \/ Li5(self)
              \/ Li6(self) \/ ncs(self)

Next == (\E self \in Proc : P(self))

(***************************************************************************)
(* Weak fairness of each process.  Because the process is a single action  *)
(* P(self), this also requires processes to eventually leave the          *)
(* noncritical section; this is harmless for checking deadlock freedom,   *)
(* since the property only concerns processes that are already trying.   *)
(***************************************************************************)
Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars(P(self))
(**************************** END TRANSLATION ******************************)

LabelSet == {"Li0", "Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b",
             "cs", "Li5", "Li6", "ncs"}

TypeOK == /\ b \in [Proc -> BOOLEAN]
          /\ c \in [Proc -> BOOLEAN]
          /\ k \in Proc
          /\ temp \in [Proc -> SUBSET Proc]
          /\ pc \in [Proc -> LabelSet]

(***************************************************************************)
(* Safety: no two distinct processes are in their critical sections.      *)
(***************************************************************************)
MutualExclusion == \A i, j \in Proc :
                      (i # j) => ~ /\ pc[i] = "cs"
                                   /\ pc[j] = "cs"

(***************************************************************************)
(* Deadlock freedom: if some process is trying to enter its critical      *)
(* section, then some process eventually enters its critical section.     *)
(* Holds under the weak fairness assumption in Spec.                      *)
(***************************************************************************)
Trying(i) == pc[i] \in {"Li1", "Li2", "Li3a", "Li3b", "Li4a", "Li4b"}

DeadlockFree == (\E i \in Proc : Trying(i)) ~> (\E j \in Proc : pc[j] = "cs")

DeadlockFreedom == \A i \in Proc :
                     (pc[i] \notin {"Li5", "Li6", "ncs"})
                        ~> (\E j \in Proc : pc[j] = "cs")

(***************************************************************************)
(* Starvation freedom: every trying process eventually enters its         *)
(* critical section.  Dijkstra's algorithm does NOT satisfy this property  *)
(* (a process can be overtaken forever), even under strong fairness, so    *)
(* model checking this property with more than one process yields a       *)
(* counterexample.                                                         *)
(***************************************************************************)
StarvationFree == \A i \in Proc :
                     (pc[i] \notin {"Li5", "Li6", "ncs"}) ~> (pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFreedom
=============================================================================
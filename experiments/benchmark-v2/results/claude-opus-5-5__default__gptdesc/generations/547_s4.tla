---------------------------- MODULE OneBitMutex ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs == 1..N

(***************************************************************************
--algorithm OneBitMutex {
   variable flag = [i \in Procs |-> FALSE] ;
   process (p \in Procs)
     variable j = 1 ;
   { ncs: while (TRUE)
          { skip ;  \* noncritical section
       e1:  flag[self] := FALSE ;
            j := 1 ;
       e2:  while (j < self)
              { if (flag[j]) { goto e1 }
                else { j := j + 1 } } ;
       e3:  flag[self] := TRUE ;
            j := 1 ;
       e4:  while (j < self)
              { if (flag[j]) { goto e1 }
                else { j := j + 1 } } ;
            j := self + 1 ;
       e5:  while (j <= N)
              { await ~flag[j] ;
                j := j + 1 } ;
       cs:  skip ;  \* critical section
       ex:  flag[self] := FALSE
          }
   }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES flag, pc, j

vars == << flag, pc, j >>

ProcSet == Procs

Init == /\ flag = [i \in Procs |-> FALSE]
        /\ j = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "e1"]
             /\ UNCHANGED << flag, j >>

e1(self) == /\ pc[self] = "e1"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) == /\ pc[self] = "e2"
            /\ IF j[self] < self
                  THEN /\ IF flag[j[self]]
                             THEN /\ pc' = [pc EXCEPT ![self] = "e1"]
                                  /\ j' = j
                             ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ j' = j
            /\ flag' = flag

e3(self) == /\ pc[self] = "e3"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "e4"]

e4(self) == /\ pc[self] = "e4"
            /\ IF j[self] < self
                  THEN /\ IF flag[j[self]]
                             THEN /\ pc' = [pc EXCEPT ![self] = "e1"]
                                  /\ j' = j
                             ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                                  /\ pc' = [pc EXCEPT ![self] = "e4"]
                  ELSE /\ j' = [j EXCEPT ![self] = self + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e5"]
            /\ flag' = flag

e5(self) == /\ pc[self] = "e5"
            /\ IF j[self] <= N
                  THEN /\ ~flag[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ j' = j
            /\ flag' = flag

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "ex"]
            /\ UNCHANGED << flag, j >>

ex(self) == /\ pc[self] = "ex"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "ncs"]
            /\ j' = j

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self)
              \/ e4(self) \/ e5(self) \/ cs(self) \/ ex(self)

Next == (\E self \in Procs : p(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ flag \in [Procs -> BOOLEAN]
          /\ j \in [Procs -> 1..(N+1)]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "e5", "cs", "ex"}]

MutualExclusion == \A i, k \in Procs : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

-----------------------------------------------------------------------------
(* Liveness (requires fairness; not implied by Spec alone) *)

FairSpec == Spec /\ \A self \in Procs : WF_vars(p(self) /\ pc[self] # "ncs")

InCS(i) == pc[i] = "cs"
Trying(i) == pc[i] \in {"e1", "e2", "e3", "e4", "e5"}

DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))

=============================================================================
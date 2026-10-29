------------------------------ MODULE Fast ------------------------------
EXTENDS Integers, TLC

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

(***************************************************************************
--algorithm Fast {
  variables x = 0, y = 0, b = [i \in 1..N |-> FALSE] ;
  process (Proc \in 1..N)
    variable j = 1 ;
  {
    ncs: while (TRUE) {
           skip ;  \* the noncritical section
    start: b[self] := TRUE ;
       l1: x := self ;
       l2: if (y # 0) { l3: b[self] := FALSE ;
                        l4: await y = 0 ;
                            goto start } ;
       l5: y := self ;
       l6: if (x # self) { l7: b[self] := FALSE ;
                               j := 1 ;
                           l8: while (j \leq N) { await ~b[j] ;
                                                 j := j + 1 } ;
                           l9: if (y # self) { l10: await y = 0 ;
                                                    goto start } } ;
       cs: skip ;  \* the critical section
      l11: y := 0 ;
      l12: b[self] := FALSE
    }
  }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc *)
        /\ j = [self \in 1..N |-> 1]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, j >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                 \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self)
                 \/ l8(self) \/ l9(self) \/ l10(self) \/ cs(self)
                 \/ l11(self) \/ l12(self)

Next == (\E self \in 1..N : Proc(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ j \in [1..N -> 1..(N+1)]
          /\ pc \in [ProcSet -> {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
                                 "l6", "l7", "l8", "l9", "l10", "cs",
                                 "l11", "l12"}]

\* Safety: no two distinct processes are in the critical section at once.
MutualExclusion == \A p, q \in ProcSet : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness (deadlock freedom): if some process is trying to enter,
\* then some process eventually enters the critical section.
Liveness == (\E i \in ProcSet : pc[i] = "start")
              ~> (\E i \in ProcSet : pc[i] = "cs")

\* Conditional liveness: assuming every process in its critical section
\* eventually leaves it, the liveness property holds.
ConditionalLiveness ==
    (\A i \in ProcSet : (pc[i] = "cs") ~> (pc[i] = "l11")) => Liveness

\* Fairness: weak fairness on every control-location action except the
\* noncritical-section (ncs) and critical-section (cs) skip steps.
Fairness ==
    \A self \in ProcSet :
        /\ WF_vars(start(self))
        /\ WF_vars(l1(self))
        /\ WF_vars(l2(self))
        /\ WF_vars(l3(self))
        /\ WF_vars(l4(self))
        /\ WF_vars(l5(self))
        /\ WF_vars(l6(self))
        /\ WF_vars(l7(self))
        /\ WF_vars(l8(self))
        /\ WF_vars(l9(self))
        /\ WF_vars(l10(self))
        /\ WF_vars(l11(self))
        /\ WF_vars(l12(self))

FairSpec == Spec /\ Fairness

THEOREM Spec => []MutualExclusion
THEOREM FairSpec => ConditionalLiveness
=============================================================================
------------------------------- MODULE Fast -------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 1..N

(***************************************************************************
--algorithm Fast {
  variables x = 0, y = 0, b = [i \in 1..N |-> FALSE] ;
  process (Proc \in 1..N)
    variable j = 1 ;
  {
ncs:  while (TRUE) {
        skip ;  \* noncritical section
start:  b[self] := TRUE ;
l1:     x := self ;
l2:     if (y # 0) {
l3:       b[self] := FALSE ;
l4:       await y = 0 ;
          goto start
        } ;
l5:     y := self ;
l6:     if (x # self) {
          b[self] := FALSE ;
          j := 1 ;
l7:       while (j <= N) {
            await ~b[j] ;
            j := j + 1
          } ;
l8:       if (y # self) {
l9:         await y = 0 ;
            goto start
          }
        } ;
cs:     skip ;  \* critical section
l10:    y := 0 ;
l11:    b[self] := FALSE
      }
  }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

ProcSet == Procs

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ j = [self \in Procs |-> 1]
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
                  THEN pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE pc' = [pc EXCEPT ![self] = "l5"]
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
                  THEN /\ b' = [b EXCEPT ![self] = FALSE]
                       /\ j' = [j EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << b, j >>
            /\ UNCHANGED << x, y >>

l7(self) == /\ pc[self] = "l7"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l8"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b >>

l8(self) == /\ pc[self] = "l8"
            /\ IF y # self
                  THEN pc' = [pc EXCEPT ![self] = "l9"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l9(self) == /\ pc[self] = "l9"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l10"]
            /\ UNCHANGED << x, y, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l11"]
             /\ UNCHANGED << x, b, j >>

l11(self) == /\ pc[self] = "l11"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
                \/ l9(self) \/ cs(self) \/ l10(self) \/ l11(self)

Next == \E self \in Procs : Proc(self)

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [Procs -> BOOLEAN]
          /\ j \in [Procs -> 1..(N+1)]
          /\ pc \in [Procs -> {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
                               "l6", "l7", "l8", "l9", "cs", "l10", "l11"}]

\* Safety: no two distinct processes are in the critical section at once.
MutualExclusion == \A i, k \in Procs : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

-----------------------------------------------------------------------------
\* Fairness: weak fairness on every control-location action except the
\* noncritical-section (ncs) and critical-section (cs) skip steps.
FairProc(self) == /\ WF_vars(start(self))
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

FSpec == Spec /\ \A self \in Procs : FairProc(self)

\* Liveness (deadlock freedom): if some process is trying to enter, then
\* some process eventually enters the critical section.
Liveness == (\E i \in Procs : pc[i] = "start")
              ~> (\E i \in Procs : pc[i] = "cs")

\* Conditional liveness: provided no process remains forever in its
\* critical section, every trying process makes the system progress.
CondLiveness == (\A i \in Procs : []<>(pc[i] # "cs")) => Liveness

\* Starvation freedom (not guaranteed by this algorithm).
StarvationFree == \A i \in Procs : (pc[i] = "start") ~> (pc[i] = "cs")

THEOREM Spec => []MutualExclusion
THEOREM FSpec => Liveness
=============================================================================
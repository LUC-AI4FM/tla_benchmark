------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

ProcSet == 1..N

(***************************************************************************
--algorithm FastMutex
{ variables x = 0, y = 0, b = [i \in 1..N |-> FALSE] ;
  process (Proc \in 1..N)
  variables j = 1, failed = FALSE ;
  { ncs: while (TRUE)
          { skip ;  \* the noncritical section
      start: b[self] := TRUE ; failed := FALSE ;
         l1: x := self ;
         l2: if (y # 0) { l3: b[self] := FALSE ;
                          l4: await y = 0 ;
                              goto start } ;
         l5: y := self ;
         l6: if (x # self) { l7: b[self] := FALSE ;
                                 j := 1 ;
                             l8: while (j \leq N) { await ~b[j] ;
                                                    j := j+1 } ;
                             l9: if (y # self) { failed := TRUE ;
                                            l10: await y = 0 ;
                                                 goto start }} ;
         cs: skip ;  \* the critical section
        l11: y := 0 ;
        l12: b[self] := FALSE } } }
***************************************************************************)

VARIABLES x, y, b, pc, j, failed

vars == << x, y, b, pc, j, failed >>

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> 1]
        /\ failed = [self \in ProcSet |-> FALSE]
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j, failed >>

start(self) == /\ pc[self] = "start"
               /\ b' = [b EXCEPT ![self] = TRUE]
               /\ failed' = [failed EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, j >>

l1(self) == /\ pc[self] = "l1"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << y, b, j, failed >>

l2(self) == /\ pc[self] = "l2"
            /\ IF y # 0
                  THEN pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, b, j, failed >>

l3(self) == /\ pc[self] = "l3"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j, failed >>

l4(self) == /\ pc[self] = "l4"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed >>

l5(self) == /\ pc[self] = "l5"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, b, j, failed >>

l6(self) == /\ pc[self] = "l6"
            /\ IF x # self
                  THEN pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, failed >>

l7(self) == /\ pc[self] = "l7"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l8"]
            /\ UNCHANGED << x, y, failed >>

l8(self) == /\ pc[self] = "l8"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b, failed >>

l9(self) == /\ pc[self] = "l9"
            /\ IF y # self
                  THEN /\ failed' = [failed EXCEPT ![self] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ failed' = failed
            /\ UNCHANGED << x, y, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j, failed >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "l11"]
            /\ UNCHANGED << x, y, b, j, failed >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j, failed >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j, failed >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                 \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
                 \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

Next == \E self \in 1..N : Proc(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))

-----------------------------------------------------------------------------

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ j \in [ProcSet -> 1..(N+1)]
          /\ failed \in [ProcSet -> BOOLEAN]
          /\ pc \in [ProcSet -> {"ncs", "start", "l1", "l2", "l3", "l4", "l5",
                                 "l6", "l7", "l8", "l9", "l10", "cs",
                                 "l11", "l12"}]

Mutex == \A i, k \in 1..N : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Liveness == []<>(\E i \in 1..N : pc[i] = "cs")

THEOREM Spec => []Mutex
=============================================================================
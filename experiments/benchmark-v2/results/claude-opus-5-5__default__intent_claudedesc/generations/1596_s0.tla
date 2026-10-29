------------------------------ MODULE FastMutexTwoGroups ------------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N \in Nat \ {0}
       /\ M \in 0..N

Procs1 == 1..M
Procs2 == (M+1)..N
Procs  == 1..N

VARIABLES x, y, b, j, pc

vars == << x, y, b, j, pc >>

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ j = [i \in Procs |-> 0]
        /\ pc = [self \in Procs |-> IF self \in Procs1 THEN "ncs" ELSE "ncs2"]

-----------------------------------------------------------------------------
(* Process type 1: processes 1..M *)

ncs(self) == /\ pc[self] = "ncs"
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
                  THEN pc' = [pc EXCEPT ![self] = "l7"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
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
                  THEN pc' = [pc EXCEPT ![self] = "l10"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
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

proc1(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
               \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
               \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

-----------------------------------------------------------------------------
(* Process type 2: processes M+1..N (identical logic, distinct labels) *)

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j >>

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "l21"]
                /\ UNCHANGED << x, y, j >>

l21(self) == /\ pc[self] = "l21"
             /\ x' = self
             /\ pc' = [pc EXCEPT ![self] = "l22"]
             /\ UNCHANGED << y, b, j >>

l22(self) == /\ pc[self] = "l22"
             /\ IF y # 0
                   THEN pc' = [pc EXCEPT ![self] = "l23"]
                   ELSE pc' = [pc EXCEPT ![self] = "l25"]
             /\ UNCHANGED << x, y, b, j >>

l23(self) == /\ pc[self] = "l23"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "l24"]
             /\ UNCHANGED << x, y, j >>

l24(self) == /\ pc[self] = "l24"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, b, j >>

l25(self) == /\ pc[self] = "l25"
             /\ y' = self
             /\ pc' = [pc EXCEPT ![self] = "l26"]
             /\ UNCHANGED << x, b, j >>

l26(self) == /\ pc[self] = "l26"
             /\ IF x # self
                   THEN pc' = [pc EXCEPT ![self] = "l27"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j >>

l27(self) == /\ pc[self] = "l27"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ j' = [j EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = "l28"]
             /\ UNCHANGED << x, y >>

l28(self) == /\ pc[self] = "l28"
             /\ IF j[self] <= N
                   THEN /\ ~b[j[self]]
                        /\ j' = [j EXCEPT ![self] = j[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "l28"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l29"]
                        /\ j' = j
             /\ UNCHANGED << x, y, b >>

l29(self) == /\ pc[self] = "l29"
             /\ IF y # self
                   THEN pc' = [pc EXCEPT ![self] = "l210"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j >>

l210(self) == /\ pc[self] = "l210"
              /\ y = 0
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j >>

cs2(self) == /\ pc[self] = "cs2"
             /\ pc' = [pc EXCEPT ![self] = "l211"]
             /\ UNCHANGED << x, y, b, j >>

l211(self) == /\ pc[self] = "l211"
              /\ y' = 0
              /\ pc' = [pc EXCEPT ![self] = "l212"]
              /\ UNCHANGED << x, b, j >>

l212(self) == /\ pc[self] = "l212"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << x, y, j >>

proc2(self) == ncs2(self) \/ start2(self) \/ l21(self) \/ l22(self) \/ l23(self)
               \/ l24(self) \/ l25(self) \/ l26(self) \/ l27(self) \/ l28(self)
               \/ l29(self) \/ l210(self) \/ cs2(self) \/ l211(self) \/ l212(self)

-----------------------------------------------------------------------------

Next == \/ (\E self \in Procs1 : proc1(self))
        \/ (\E self \in Procs2 : proc2(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs1 : WF_vars(proc1(self))
        /\ \A self \in Procs2 : WF_vars(proc2(self))

-----------------------------------------------------------------------------

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [Procs -> BOOLEAN]
          /\ j \in [Procs -> 0..(N+1)]

InCS(i) == pc[i] \in {"cs", "cs2"}

MutualExclusion == \A i, k \in Procs : (i # k) => ~(InCS(i) /\ InCS(k))

Liveness == []<>(\E i \in Procs : InCS(i))

=============================================================================
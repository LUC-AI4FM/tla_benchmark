---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES x, y, b, pc, j, failed, j2, failed2

vars == << x, y, b, pc, j, failed, j2, failed2 >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in {1} |-> 1]
        /\ failed = [self \in {1} |-> FALSE]
        /\ j2 = [self \in 2..N |-> 1]
        /\ failed2 = [self \in 2..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "ncs1"
                                        [] self \in 2..N -> "ncs2"]

(***************************************************************************)
(* Process 1                                                               *)
(***************************************************************************)

ncs1 == /\ pc[1] = "ncs1"
        /\ pc' = [pc EXCEPT ![1] = "start1"]
        /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

start1 == /\ pc[1] = "start1"
          /\ b' = [b EXCEPT ![1] = TRUE]
          /\ failed' = [failed EXCEPT ![1] = FALSE]
          /\ pc' = [pc EXCEPT ![1] = "wx1"]
          /\ UNCHANGED << x, y, j, j2, failed2 >>

wx1 == /\ pc[1] = "wx1"
       /\ x' = 1
       /\ pc' = [pc EXCEPT ![1] = "ry1"]
       /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

ry1 == /\ pc[1] = "ry1"
       /\ IF y # 0
            THEN pc' = [pc EXCEPT ![1] = "bk1"]
            ELSE pc' = [pc EXCEPT ![1] = "wy1"]
       /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

bk1 == /\ pc[1] = "bk1"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "aw1"]
       /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

aw1 == /\ pc[1] = "aw1"
       /\ y = 0
       /\ pc' = [pc EXCEPT ![1] = "start1"]
       /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

wy1 == /\ pc[1] = "wy1"
       /\ y' = 1
       /\ pc' = [pc EXCEPT ![1] = "rx1"]
       /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

rx1 == /\ pc[1] = "rx1"
       /\ IF x # 1
            THEN pc' = [pc EXCEPT ![1] = "cl1"]
            ELSE pc' = [pc EXCEPT ![1] = "ent1"]
       /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

cl1 == /\ pc[1] = "cl1"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ j' = [j EXCEPT ![1] = 1]
       /\ pc' = [pc EXCEPT ![1] = "lp1"]
       /\ UNCHANGED << x, y, failed, j2, failed2 >>

lp1 == /\ pc[1] = "lp1"
       /\ IF j[1] <= N
            THEN /\ (j[1] = 1 \/ ~b[j[1]])
                 /\ j' = [j EXCEPT ![1] = j[1] + 1]
                 /\ pc' = [pc EXCEPT ![1] = "lp1"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "own1"]
                 /\ UNCHANGED j
       /\ UNCHANGED << x, y, b, failed, j2, failed2 >>

own1 == /\ pc[1] = "own1"
        /\ IF y # 1
             THEN /\ failed' = [failed EXCEPT ![1] = TRUE]
                  /\ pc' = [pc EXCEPT ![1] = "ay1"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "ent1"]
                  /\ UNCHANGED failed
        /\ UNCHANGED << x, y, b, j, j2, failed2 >>

ay1 == /\ pc[1] = "ay1"
       /\ y = 0
       /\ pc' = [pc EXCEPT ![1] = "ent1"]
       /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

ent1 == /\ pc[1] = "ent1"
        /\ IF ~failed[1]
             THEN pc' = [pc EXCEPT ![1] = "cs1"]
             ELSE pc' = [pc EXCEPT ![1] = "start1"]
        /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

cs1 == /\ pc[1] = "cs1"
       /\ pc' = [pc EXCEPT ![1] = "ry0_1"]
       /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

ry0_1 == /\ pc[1] = "ry0_1"
         /\ y' = 0
         /\ pc' = [pc EXCEPT ![1] = "rb1"]
         /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

rb1 == /\ pc[1] = "rb1"
       /\ b' = [b EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "ncs1"]
       /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc1 == ncs1 \/ start1 \/ wx1 \/ ry1 \/ bk1 \/ aw1 \/ wy1 \/ rx1
           \/ cl1 \/ lp1 \/ own1 \/ ay1 \/ ent1 \/ cs1 \/ ry0_1 \/ rb1

(***************************************************************************)
(* Processes 2..N                                                          *)
(***************************************************************************)

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ failed2' = [failed2 EXCEPT ![self] = FALSE]
                /\ pc' = [pc EXCEPT ![self] = "wx2"]
                /\ UNCHANGED << x, y, j, failed, j2 >>

wx2(self) == /\ pc[self] = "wx2"
             /\ x' = self
             /\ pc' = [pc EXCEPT ![self] = "ry2"]
             /\ UNCHANGED << y, b, j, failed, j2, failed2 >>

ry2(self) == /\ pc[self] = "ry2"
             /\ IF y # 0
                  THEN pc' = [pc EXCEPT ![self] = "bk2"]
                  ELSE pc' = [pc EXCEPT ![self] = "wy2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

bk2(self) == /\ pc[self] = "bk2"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "aw2"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

aw2(self) == /\ pc[self] = "aw2"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

wy2(self) == /\ pc[self] = "wy2"
             /\ y' = self
             /\ pc' = [pc EXCEPT ![self] = "rx2"]
             /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

rx2(self) == /\ pc[self] = "rx2"
             /\ IF x # self
                  THEN pc' = [pc EXCEPT ![self] = "cl2"]
                  ELSE pc' = [pc EXCEPT ![self] = "ent2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

cl2(self) == /\ pc[self] = "cl2"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ j2' = [j2 EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = "lp2"]
             /\ UNCHANGED << x, y, j, failed, failed2 >>

lp2(self) == /\ pc[self] = "lp2"
             /\ IF j2[self] <= N
                  THEN /\ (j2[self] = self \/ ~b[j2[self]])
                       /\ j2' = [j2 EXCEPT ![self] = j2[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "lp2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "own2"]
                       /\ UNCHANGED j2
             /\ UNCHANGED << x, y, b, j, failed, failed2 >>

own2(self) == /\ pc[self] = "own2"
              /\ IF y # self
                   THEN /\ failed2' = [failed2 EXCEPT ![self] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = "ay2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ent2"]
                        /\ UNCHANGED failed2
              /\ UNCHANGED << x, y, b, j, failed, j2 >>

ay2(self) == /\ pc[self] = "ay2"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "ent2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

ent2(self) == /\ pc[self] = "ent2"
              /\ IF ~failed2[self]
                   THEN pc' = [pc EXCEPT ![self] = "cs2"]
                   ELSE pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

cs2(self) == /\ pc[self] = "cs2"
             /\ pc' = [pc EXCEPT ![self] = "ry0_2"]
             /\ UNCHANGED << x, y, b, j, failed, j2, failed2 >>

ry0_2(self) == /\ pc[self] = "ry0_2"
               /\ y' = 0
               /\ pc' = [pc EXCEPT ![self] = "rb2"]
               /\ UNCHANGED << x, b, j, failed, j2, failed2 >>

rb2(self) == /\ pc[self] = "rb2"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs2"]
             /\ UNCHANGED << x, y, j, failed, j2, failed2 >>

Proc2(self) == ncs2(self) \/ start2(self) \/ wx2(self) \/ ry2(self)
                 \/ bk2(self) \/ aw2(self) \/ wy2(self) \/ rx2(self)
                 \/ cl2(self) \/ lp2(self) \/ own2(self) \/ ay2(self)
                 \/ ent2(self) \/ cs2(self) \/ ry0_2(self) \/ rb2(self)

Next == Proc1 \/ (\E self \in 2..N : Proc2(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(Proc2(self))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

InCS(i) == pc[i] \in {"cs1", "cs2"}

Invariant == \A i, k \in ProcSet : (i # k) => ~(InCS(i) /\ InCS(k))

Liveness == []<>(\E i \in ProcSet : InCS(i))

=============================================================================
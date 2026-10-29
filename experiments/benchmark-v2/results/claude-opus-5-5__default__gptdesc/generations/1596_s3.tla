---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers

CONSTANTS M, N

ASSUME /\ N \in Nat
       /\ M \in 0..N

VARIABLES x, y, b, j, pc

vars == << x, y, b, j, pc >>

ProcSet == (1..M) \cup ((M+1)..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..M     -> "ncs"
                                       [] self \in (M+1)..N -> "ncs2"]

(***************************************************************************)
(* First process class: processes in 1..M                                  *)
(***************************************************************************)

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

p1(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
              \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
              \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

(***************************************************************************)
(* Second process class: processes in (M+1)..N                             *)
(***************************************************************************)

ncs2(self) == /\ pc[self] = "ncs2"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j >>

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "l12a"]
                /\ UNCHANGED << x, y, j >>

l12a(self) == /\ pc[self] = "l12a"
              /\ x' = self
              /\ pc' = [pc EXCEPT ![self] = "l22"]
              /\ UNCHANGED << y, b, j >>

l22(self) == /\ pc[self] = "l22"
             /\ IF y # 0
                   THEN pc' = [pc EXCEPT ![self] = "l32"]
                   ELSE pc' = [pc EXCEPT ![self] = "l52"]
             /\ UNCHANGED << x, y, b, j >>

l32(self) == /\ pc[self] = "l32"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "l42"]
             /\ UNCHANGED << x, y, j >>

l42(self) == /\ pc[self] = "l42"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, b, j >>

l52(self) == /\ pc[self] = "l52"
             /\ y' = self
             /\ pc' = [pc EXCEPT ![self] = "l62"]
             /\ UNCHANGED << x, b, j >>

l62(self) == /\ pc[self] = "l62"
             /\ IF x # self
                   THEN pc' = [pc EXCEPT ![self] = "l72"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j >>

l72(self) == /\ pc[self] = "l72"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ j' = [j EXCEPT ![self] = 1]
             /\ pc' = [pc EXCEPT ![self] = "l82"]
             /\ UNCHANGED << x, y >>

l82(self) == /\ pc[self] = "l82"
             /\ IF j[self] <= N
                   THEN /\ ~b[j[self]]
                        /\ j' = [j EXCEPT ![self] = j[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "l82"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l92"]
                        /\ j' = j
             /\ UNCHANGED << x, y, b >>

l92(self) == /\ pc[self] = "l92"
             /\ IF y # self
                   THEN pc' = [pc EXCEPT ![self] = "l102"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j >>

l102(self) == /\ pc[self] = "l102"
              /\ y = 0
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j >>

cs2(self) == /\ pc[self] = "cs2"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "l112"]
             /\ UNCHANGED << x, y, b, j >>

l112(self) == /\ pc[self] = "l112"
              /\ y' = 0
              /\ pc' = [pc EXCEPT ![self] = "l122"]
              /\ UNCHANGED << x, b, j >>

l122(self) == /\ pc[self] = "l122"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << x, y, j >>

p2(self) == ncs2(self) \/ start2(self) \/ l12a(self) \/ l22(self)
              \/ l32(self) \/ l42(self) \/ l52(self) \/ l62(self)
              \/ l72(self) \/ l82(self) \/ l92(self) \/ l102(self)
              \/ cs2(self) \/ l112(self) \/ l122(self)

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)

Next == (\E self \in 1..M : p1(self))
        \/ (\E self \in (M+1)..N : p2(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 1..M : WF_vars(p1(self))
        /\ \A self \in (M+1)..N : WF_vars(p2(self))

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

InCS(i) == pc[i] \in {"cs", "cs2"}

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ j \in [ProcSet -> 0..(N+1)]

MutualExclusion == \A i, k \in ProcSet : (i # k) => ~(InCS(i) /\ InCS(k))

StarvationFree == []<>(\E i \in ProcSet : InCS(i))

THEOREM Spec => []MutualExclusion
=============================================================================
---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ M <= N

VARIABLES x, y, b, j, pc

vars == << x, y, b, j, pc >>

ProcSet == (1..M) \cup ((M+1)..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> 0]
        /\ pc = [self \in ProcSet |-> IF self \in 1..M THEN "ncs" ELSE "ncs2"]

\* ---------------- First process class: 1..M ----------------

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
                  THEN /\ b' = [b EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "l3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
                       /\ b' = b
            /\ UNCHANGED << x, y, j >>

l3(self) == /\ pc[self] = "l3"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j >>

l4(self) == /\ pc[self] = "l4"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, b, j >>

l5(self) == /\ pc[self] = "l5"
            /\ IF x # self
                  THEN /\ b' = [b EXCEPT ![self] = FALSE]
                       /\ j' = [j EXCEPT ![self] = 1]
                       /\ pc' = [pc EXCEPT ![self] = "l6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ UNCHANGED << b, j >>
            /\ UNCHANGED << x, y >>

l6(self) == /\ pc[self] = "l6"
            /\ IF j[self] <= N
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "l6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b >>

l7(self) == /\ pc[self] = "l7"
            /\ IF y # self
                  THEN pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j >>

l8(self) == /\ pc[self] = "l8"
            /\ y = 0
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << x, y, b, j >>

l9(self) == /\ pc[self] = "l9"
            /\ y' = 0
            /\ pc' = [pc EXCEPT ![self] = "l10"]
            /\ UNCHANGED << x, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

Proc(self) == \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self)
              \/ l3(self) \/ l4(self) \/ l5(self) \/ l6(self)
              \/ l7(self) \/ l8(self) \/ cs(self) \/ l9(self)
              \/ l10(self)

\* ---------------- Second process class: (M+1)..N ----------------

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED << x, y, b, j >>

start2(self) == /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ pc' = [pc EXCEPT ![self] = "l12"]
                /\ UNCHANGED << x, y, j >>

l12(self) == /\ pc[self] = "l12"
             /\ x' = self
             /\ pc' = [pc EXCEPT ![self] = "l22"]
             /\ UNCHANGED << y, b, j >>

l22(self) == /\ pc[self] = "l22"
             /\ IF y # 0
                   THEN /\ b' = [b EXCEPT ![self] = FALSE]
                        /\ pc' = [pc EXCEPT ![self] = "l32"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l42"]
                        /\ b' = b
             /\ UNCHANGED << x, y, j >>

l32(self) == /\ pc[self] = "l32"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, b, j >>

l42(self) == /\ pc[self] = "l42"
             /\ y' = self
             /\ pc' = [pc EXCEPT ![self] = "l52"]
             /\ UNCHANGED << x, b, j >>

l52(self) == /\ pc[self] = "l52"
             /\ IF x # self
                   THEN /\ b' = [b EXCEPT ![self] = FALSE]
                        /\ j' = [j EXCEPT ![self] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "l62"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                        /\ UNCHANGED << b, j >>
             /\ UNCHANGED << x, y >>

l62(self) == /\ pc[self] = "l62"
             /\ IF j[self] <= N
                   THEN /\ ~b[j[self]]
                        /\ j' = [j EXCEPT ![self] = j[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "l62"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "l72"]
                        /\ j' = j
             /\ UNCHANGED << x, y, b >>

l72(self) == /\ pc[self] = "l72"
             /\ IF y # self
                   THEN pc' = [pc EXCEPT ![self] = "l82"]
                   ELSE pc' = [pc EXCEPT ![self] = "cs2"]
             /\ UNCHANGED << x, y, b, j >>

l82(self) == /\ pc[self] = "l82"
             /\ y = 0
             /\ pc' = [pc EXCEPT ![self] = "start2"]
             /\ UNCHANGED << x, y, b, j >>

cs2(self) == /\ pc[self] = "cs2"
             /\ pc' = [pc EXCEPT ![self] = "l92"]
             /\ UNCHANGED << x, y, b, j >>

l92(self) == /\ pc[self] = "l92"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l102"]
             /\ UNCHANGED << x, b, j >>

l102(self) == /\ pc[self] = "l102"
              /\ b' = [b EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << x, y, j >>

Proc2(self) == \/ ncs2(self) \/ start2(self) \/ l12(self) \/ l22(self)
               \/ l32(self) \/ l42(self) \/ l52(self) \/ l62(self)
               \/ l72(self) \/ l82(self) \/ cs2(self) \/ l92(self)
               \/ l102(self)

\* ---------------- Specification ----------------

Next == \/ (\E self \in 1..M : Proc(self))
        \/ (\E self \in (M+1)..N : Proc2(self))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 1..M : WF_vars(Proc(self))
        /\ \A self \in (M+1)..N : WF_vars(Proc2(self))

InCS(i) == pc[i] \in {"cs", "cs2"}

Invariant == \A i, k \in ProcSet : (i # k) => ~(InCS(i) /\ InCS(k))

Liveness == []<>(\E i \in ProcSet : InCS(i))

=============================================================================
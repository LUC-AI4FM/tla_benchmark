---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES x, y, b, j, pc

vars == << x, y, b, j, pc >>

ProcSet == {1} \cup (2..N)

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [i \in ProcSet |-> 0]
        /\ pc = [i \in ProcSet |-> "start"]

----------------------------------------------------------------------------
(* The special process with identity 1 *)

p1start == /\ pc[1] = "start"
           /\ b' = [b EXCEPT ![1] = TRUE]
           /\ pc' = [pc EXCEPT ![1] = "l1"]
           /\ UNCHANGED << x, y, j >>

p1l1 == /\ pc[1] = "l1"
        /\ x' = 1
        /\ pc' = [pc EXCEPT ![1] = "l2"]
        /\ UNCHANGED << y, b, j >>

p1l2 == /\ pc[1] = "l2"
        /\ IF y # 0
              THEN /\ b' = [b EXCEPT ![1] = FALSE]
                   /\ pc' = [pc EXCEPT ![1] = "l3"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "l4"]
                   /\ b' = b
        /\ UNCHANGED << x, y, j >>

p1l3 == /\ pc[1] = "l3"
        /\ y = 0
        /\ pc' = [pc EXCEPT ![1] = "start"]
        /\ UNCHANGED << x, y, b, j >>

p1l4 == /\ pc[1] = "l4"
        /\ y' = 1
        /\ pc' = [pc EXCEPT ![1] = "l5"]
        /\ UNCHANGED << x, b, j >>

p1l5 == /\ pc[1] = "l5"
        /\ IF x # 1
              THEN /\ b' = [b EXCEPT ![1] = FALSE]
                   /\ j' = [j EXCEPT ![1] = 1]
                   /\ pc' = [pc EXCEPT ![1] = "l6"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "cs"]
                   /\ UNCHANGED << b, j >>
        /\ UNCHANGED << x, y >>

p1l6 == /\ pc[1] = "l6"
        /\ IF j[1] <= N
              THEN /\ ~b[j[1]]
                   /\ j' = [j EXCEPT ![1] = j[1] + 1]
                   /\ pc' = [pc EXCEPT ![1] = "l6"]
              ELSE /\ pc' = [pc EXCEPT ![1] = "l7"]
                   /\ j' = j
        /\ UNCHANGED << x, y, b >>

p1l7 == /\ pc[1] = "l7"
        /\ IF y # 1
              THEN pc' = [pc EXCEPT ![1] = "l8"]
              ELSE pc' = [pc EXCEPT ![1] = "cs"]
        /\ UNCHANGED << x, y, b, j >>

p1l8 == /\ pc[1] = "l8"
        /\ y = 0
        /\ pc' = [pc EXCEPT ![1] = "start"]
        /\ UNCHANGED << x, y, b, j >>

p1cs == /\ pc[1] = "cs"
        /\ TRUE
        /\ pc' = [pc EXCEPT ![1] = "l9"]
        /\ UNCHANGED << x, y, b, j >>

p1l9 == /\ pc[1] = "l9"
        /\ y' = 0
        /\ pc' = [pc EXCEPT ![1] = "l10"]
        /\ UNCHANGED << x, b, j >>

p1l10 == /\ pc[1] = "l10"
         /\ b' = [b EXCEPT ![1] = FALSE]
         /\ pc' = [pc EXCEPT ![1] = "start"]
         /\ UNCHANGED << x, y, j >>

Proc1 == p1start \/ p1l1 \/ p1l2 \/ p1l3 \/ p1l4 \/ p1l5 \/ p1l6
         \/ p1l7 \/ p1l8 \/ p1cs \/ p1l9 \/ p1l10

----------------------------------------------------------------------------
(* The parameterized processes with identities 2..N *)

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
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << x, y, b, j >>

l9(self) == /\ pc[self] = "l9"
            /\ y' = 0
            /\ pc' = [pc EXCEPT ![self] = "l10"]
            /\ UNCHANGED << x, b, j >>

l10(self) == /\ pc[self] = "l10"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, j >>

P(self) == start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
           \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self) \/ cs(self)
           \/ l9(self) \/ l10(self)

----------------------------------------------------------------------------

Next == Proc1 \/ (\E self \in 2..N : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Proc1)
        /\ \A self \in 2..N : WF_vars(P(self))

----------------------------------------------------------------------------

Invariant == \A i, k \in ProcSet : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Liveness == []<>(\E i \in ProcSet : pc[i] = "cs")

=============================================================================
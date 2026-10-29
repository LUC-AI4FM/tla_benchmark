------------------------------ MODULE FastMutex ------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

VARIABLES x, y, b, pc, S

vars == << x, y, b, pc, S >>

ProcSet == 1..N

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in 1..N |-> FALSE]
    /\ S = [self \in ProcSet |-> {}]
    /\ pc = [self \in ProcSet |-> "start"]

start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED << x, y, S >>

l1(self) ==
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED << y, b, S >>

l2(self) ==
    /\ pc[self] = "l2"
    /\ IF y # 0
          THEN pc' = [pc EXCEPT ![self] = "l3"]
          ELSE pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, y, b, S >>

l3(self) ==
    /\ pc[self] = "l3"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "l4"]
    /\ UNCHANGED << x, y, S >>

l4(self) ==
    /\ pc[self] = "l4"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, S >>

l5(self) ==
    /\ pc[self] = "l5"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l6"]
    /\ UNCHANGED << x, b, S >>

l6(self) ==
    /\ pc[self] = "l6"
    /\ IF x # self
          THEN pc' = [pc EXCEPT ![self] = "l7"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, S >>

l7(self) ==
    /\ pc[self] = "l7"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ S' = [S EXCEPT ![self] = (1..N) \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "l8"]
    /\ UNCHANGED << x, y >>

l8(self) ==
    /\ pc[self] = "l8"
    /\ IF S[self] # {}
          THEN /\ \E j \in S[self] :
                    /\ ~b[j]
                    /\ S' = [S EXCEPT ![self] = S[self] \ {j}]
               /\ pc' = [pc EXCEPT ![self] = "l8"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
               /\ S' = S
    /\ UNCHANGED << x, y, b >>

l9(self) ==
    /\ pc[self] = "l9"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l10"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, S >>

l10(self) ==
    /\ pc[self] = "l10"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, S >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ TRUE
    /\ pc' = [pc EXCEPT ![self] = "l11"]
    /\ UNCHANGED << x, y, b, S >>

l11(self) ==
    /\ pc[self] = "l11"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l12"]
    /\ UNCHANGED << x, b, S >>

l12(self) ==
    /\ pc[self] = "l12"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, S >>

Proc(self) ==
    \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
    \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self) \/ l9(self)
    \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

Next == \E self \in 1..N : Proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))

Invariant == \A i, j \in 1..N : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness == []<>(\E i \in 1..N : pc[i] = "cs")

=============================================================================
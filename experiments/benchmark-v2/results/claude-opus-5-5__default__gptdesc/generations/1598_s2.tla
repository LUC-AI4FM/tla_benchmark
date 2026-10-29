------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

ProcSet == 1..N

VARIABLES x, y, b, S, pc

vars == << x, y, b, S, pc >>

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [ProcSet -> BOOLEAN]
    /\ S \in [ProcSet -> SUBSET ProcSet]
    /\ pc \in [ProcSet -> {"ncs", "start", "l1", "l2", "l3", "l3a", "l4",
                           "l5", "l6", "l7", "l8", "l9", "cs", "l10", "l11"}]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ S = [i \in ProcSet |-> {}]
    /\ pc = [i \in ProcSet |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, S >>

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
          ELSE pc' = [pc EXCEPT ![self] = "l4"]
    /\ UNCHANGED << x, y, b, S >>

l3(self) ==
    /\ pc[self] = "l3"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "l3a"]
    /\ UNCHANGED << x, y, S >>

l3a(self) ==
    /\ pc[self] = "l3a"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, S >>

l4(self) ==
    /\ pc[self] = "l4"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, b, S >>

l5(self) ==
    /\ pc[self] = "l5"
    /\ IF x # self
          THEN pc' = [pc EXCEPT ![self] = "l6"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, S >>

l6(self) ==
    /\ pc[self] = "l6"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ S' = [S EXCEPT ![self] = ProcSet \ {self}]
    /\ pc' = [pc EXCEPT ![self] = "l7"]
    /\ UNCHANGED << x, y >>

l7(self) ==
    /\ pc[self] = "l7"
    /\ IF S[self] # {}
          THEN /\ \E j \in S[self] :
                    /\ ~b[j]
                    /\ S' = [S EXCEPT ![self] = S[self] \ {j}]
               /\ pc' = [pc EXCEPT ![self] = "l7"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l8"]
               /\ S' = S
    /\ UNCHANGED << x, y, b >>

l8(self) ==
    /\ pc[self] = "l8"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l9"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, S >>

l9(self) ==
    /\ pc[self] = "l9"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, S >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "l10"]
    /\ UNCHANGED << x, y, b, S >>

l10(self) ==
    /\ pc[self] = "l10"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l11"]
    /\ UNCHANGED << x, b, S >>

l11(self) ==
    /\ pc[self] = "l11"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << x, y, S >>

proc(self) ==
    \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
    \/ l3a(self) \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self)
    \/ l8(self) \/ l9(self) \/ cs(self) \/ l10(self) \/ l11(self)

Next == \E self \in ProcSet : proc(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion ==
    \A i, j \in ProcSet : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness == []<>(\E i \in ProcSet : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================
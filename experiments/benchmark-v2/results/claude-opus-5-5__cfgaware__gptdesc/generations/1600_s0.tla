------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N, defaultInitValue

ASSUME N \in Nat /\ N >= 1

ProcSet == 1..N

VARIABLES x, y, b, pc, j, failed

vars == << x, y, b, pc, j, failed >>

Init == /\ x = defaultInitValue
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        /\ j = [self \in ProcSet |-> defaultInitValue]
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
            /\ failed' = [failed EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED << x, y, j >>

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
                  ELSE /\ failed' = failed
                       /\ pc' = [pc EXCEPT ![self] = "cs"]
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
             /\ failed' = [failed EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "ncs"]
             /\ UNCHANGED << x, y, j >>

Proc(self) == ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
                 \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
                 \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

Next == \E self \in 1..N : Proc(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))

InCS == {i \in 1..N : pc[i] = "cs"}

Invariant == \A i, k \in 1..N : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

SomeoneInCS == \E i \in 1..N : pc[i] = "cs"

Liveness == []<>SomeoneInCS

Contention == \E i, k \in 1..N : i # k /\ b[i] /\ b[k]

PossibleCounts == Cardinality(InCS) \in {0, 1}

_POSSIBLE == PossibleCounts /\ (SomeoneInCS \/ Contention \/ ~SomeoneInCS)

=============================================================================
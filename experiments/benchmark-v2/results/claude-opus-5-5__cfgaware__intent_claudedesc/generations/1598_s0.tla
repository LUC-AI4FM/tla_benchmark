---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

ProcSet == 1..N

VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ pc = [i \in ProcSet |-> "ncs"]
    /\ j = [i \in ProcSet |-> 1]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED << x, y, j >>

l1(self) ==
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED << y, b, j >>

l2(self) ==
    /\ pc[self] = "l2"
    /\ IF y # 0
          THEN /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "l3"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
               /\ b' = b
    /\ UNCHANGED << x, y, j >>

l3(self) ==
    /\ pc[self] = "l3"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

l4(self) ==
    /\ pc[self] = "l4"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, b, j >>

l5(self) ==
    /\ pc[self] = "l5"
    /\ IF x # self
          THEN /\ b' = [b EXCEPT ![self] = FALSE]
               /\ j' = [j EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "l6"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED << b, j >>
    /\ UNCHANGED << x, y >>

l6(self) ==
    /\ pc[self] = "l6"
    /\ IF j[self] <= N
          THEN /\ ~b[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "l6"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
               /\ j' = j
    /\ UNCHANGED << x, y, b >>

l7(self) ==
    /\ pc[self] = "l7"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l3"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "l8"]
    /\ UNCHANGED << x, y, b, j >>

l8(self) ==
    /\ pc[self] = "l8"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l9"]
    /\ UNCHANGED << x, b, j >>

l9(self) ==
    /\ pc[self] = "l9"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << x, y, j >>

proc(self) ==
    \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
    \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ cs(self)
    \/ l8(self) \/ l9(self)

Next == \E self \in ProcSet : proc(self)

Spec == Init /\ [][Next]_vars /\ \A self \in ProcSet : WF_vars(proc(self))

Invariant ==
    \A i, k \in ProcSet : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Liveness == []<>(\E i \in ProcSet : pc[i] = "cs")

=============================================================================
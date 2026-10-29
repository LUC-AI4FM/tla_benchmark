------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES x, y, b, pc, j

vars == << x, y, b, pc, j >>

ProcSet == 1..N

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in 1..N |-> FALSE]
    /\ j = [self \in ProcSet |-> 0]
    /\ pc = [self \in ProcSet |-> "ncs"]

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
          THEN pc' = [pc EXCEPT ![self] = "l3"]
          ELSE pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED << x, y, b, j >>

l3(self) ==
    /\ pc[self] = "l3"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "l4"]
    /\ UNCHANGED << x, y, j >>

l4(self) ==
    /\ pc[self] = "l4"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

l5(self) ==
    /\ pc[self] = "l5"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l6"]
    /\ UNCHANGED << x, b, j >>

l6(self) ==
    /\ pc[self] = "l6"
    /\ IF x # self
          THEN pc' = [pc EXCEPT ![self] = "l7"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

l7(self) ==
    /\ pc[self] = "l7"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "l8"]
    /\ UNCHANGED << x, y >>

l8(self) ==
    /\ pc[self] = "l8"
    /\ IF j[self] <= N
          THEN /\ ~b[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "l8"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l9"]
               /\ UNCHANGED j
    /\ UNCHANGED << x, y, b >>

l9(self) ==
    /\ pc[self] = "l9"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l10"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << x, y, b, j >>

l10(self) ==
    /\ pc[self] = "l10"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED << x, y, b, j >>

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "l11"]
    /\ UNCHANGED << x, y, b, j >>

l11(self) ==
    /\ pc[self] = "l11"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l12"]
    /\ UNCHANGED << x, b, j >>

l12(self) ==
    /\ pc[self] = "l12"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << x, y, j >>

Proc(self) ==
    \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
    \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
    \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

Next == \E self \in ProcSet : Proc(self)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

Invariant ==
    \A i, k \in 1..N : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

Liveness ==
    \A i \in 1..N : (pc[i] = "start") ~> (\E k \in 1..N : pc[k] = "cs")

CondLiveness ==
    (\A i \in 1..N : []<>(pc[i] # "cs")) => Liveness

FairSpec ==
    /\ Spec
    /\ \A self \in ProcSet :
          /\ WF_vars(start(self))
          /\ WF_vars(l1(self))
          /\ WF_vars(l2(self))
          /\ WF_vars(l3(self))
          /\ WF_vars(l4(self))
          /\ WF_vars(l5(self))
          /\ WF_vars(l6(self))
          /\ WF_vars(l7(self))
          /\ WF_vars(l8(self))
          /\ WF_vars(l9(self))
          /\ WF_vars(l10(self))
          /\ WF_vars(l11(self))
          /\ WF_vars(l12(self))

=============================================================================
---------------------------- MODULE OneBitMutex ----------------------------
EXTENDS Integers

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0 .. (N - 1)

VARIABLES flag, pc, j

vars == << flag, pc, j >>

Init ==
    /\ flag = [p \in Procs |-> FALSE]
    /\ j = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, j >>

e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ j' = [j EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]

e2(self) ==
    /\ pc[self] = "e2"
    /\ IF j[self] < self
          THEN IF flag[j[self]]
                  THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED j
                  ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
          ELSE /\ j' = [j EXCEPT ![self] = self + 1]
               /\ pc' = [pc EXCEPT ![self] = "e5"]
    /\ UNCHANGED flag

e3(self) ==
    /\ pc[self] = "e3"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED j

e4(self) ==
    /\ pc[self] = "e4"
    /\ ~flag[j[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, j >>

e5(self) ==
    /\ pc[self] = "e5"
    /\ IF j[self] < N
          THEN /\ ~flag[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "e5"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED j
    /\ UNCHANGED flag

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "ex"]
    /\ UNCHANGED << flag, j >>

ex(self) ==
    /\ pc[self] = "ex"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED j

P(self) ==
    \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
    \/ e5(self) \/ cs(self) \/ ex(self)

Next == \E self \in Procs : P(self)

Spec == Init /\ [][Next]_vars

=============================================================================
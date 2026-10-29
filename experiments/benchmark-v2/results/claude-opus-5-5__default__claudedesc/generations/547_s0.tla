---------------------------- MODULE OneBitMutex ----------------------------
EXTENDS Integers

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs == 0 .. (N - 1)

VARIABLES flag, pc, j

vars == << flag, pc, j >>

TypeOK ==
    /\ flag \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "e5", "cs", "ex"}]
    /\ j \in [Procs -> 0 .. N]

Init ==
    /\ flag = [i \in Procs |-> FALSE]
    /\ pc = [self \in Procs |-> "ncs"]
    /\ j = [self \in Procs |-> 0]

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
                       /\ j' = j
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
    /\ ~ flag[j[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, j >>

e5(self) ==
    /\ pc[self] = "e5"
    /\ IF j[self] < N
          THEN /\ ~ flag[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "e5"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ j' = j
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

p(self) == ncs(self) \/ e1(self) \/ e2(self) \/ e3(self)
              \/ e4(self) \/ e5(self) \/ cs(self) \/ ex(self)

Next == \E self \in Procs : p(self)

Spec == Init /\ [][Next]_vars

\* Not checked by the configuration; provided for reference only.
MutualExclusion == \A a, b \in Procs : (a # b) => ~(pc[a] = "cs" /\ pc[b] = "cs")

=============================================================================
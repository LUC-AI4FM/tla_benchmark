------------------------------- MODULE OneBit -------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs == 0..(N-1)

VARIABLES flag, pc, j

vars == << flag, pc, j >>

TypeOK ==
    /\ flag \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3", "e4", "e5", "cs", "exit"}]
    /\ j \in [Procs -> 0..N]

Init ==
    /\ flag = [p \in Procs |-> FALSE]
    /\ pc = [p \in Procs |-> "ncs"]
    /\ j = [p \in Procs |-> 0]

\* Non-critical section
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << flag, j >>

\* Raise own flag and start scanning lower-indexed processes
e1(self) ==
    /\ pc[self] = "e1"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ j' = [j EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]

\* Scan lower-indexed processes
e2(self) ==
    /\ pc[self] = "e2"
    /\ IF j[self] < self
          THEN IF flag[j[self]]
                  THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                       /\ UNCHANGED << flag, j >>
                  ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "e2"]
                       /\ UNCHANGED flag
          ELSE /\ j' = [j EXCEPT ![self] = self + 1]
               /\ pc' = [pc EXCEPT ![self] = "e5"]
               /\ UNCHANGED flag

\* Back off: lower own flag
e3(self) ==
    /\ pc[self] = "e3"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "e4"]
    /\ UNCHANGED j

\* Wait for the conflicting lower-indexed flag to clear, then restart
e4(self) ==
    /\ pc[self] = "e4"
    /\ ~flag[j[self]]
    /\ j' = [j EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED flag

\* Wait for all higher-indexed processes' flags to be lowered
e5(self) ==
    /\ pc[self] = "e5"
    /\ IF j[self] < N
          THEN /\ ~flag[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "e5"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED j
    /\ UNCHANGED flag

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << flag, j >>

\* Exit protocol: lower flag and reset index
exit(self) ==
    /\ pc[self] = "exit"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]

proc(self) ==
    \/ ncs(self) \/ e1(self) \/ e2(self) \/ e3(self)
    \/ e4(self) \/ e5(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : proc(self)

Fairness ==
    \A self \in Procs :
        WF_vars(e1(self) \/ e2(self) \/ e3(self) \/ e4(self)
                \/ e5(self) \/ cs(self) \/ exit(self))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Auxiliary definition (not stated as a checked property in the description)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

=============================================================================
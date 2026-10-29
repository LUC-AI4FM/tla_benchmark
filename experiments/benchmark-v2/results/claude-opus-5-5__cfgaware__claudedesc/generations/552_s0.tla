------------------------------- MODULE OneBitMutex -------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 0..(N-1)

VARIABLES flag, pc, j

vars == <<flag, pc, j>>

TypeOK ==
    /\ flag \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> {"ncs", "enter", "e2", "e3", "e4", "e5", "cs", "exit"}]
    /\ j \in [Procs -> 0..N]

Init ==
    /\ flag = [p \in Procs |-> FALSE]
    /\ pc = [p \in Procs |-> "ncs"]
    /\ j = [p \in Procs |-> 0]

\* Non-critical section: may decide to try to enter
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED <<flag, j>>

\* Raise own flag and start scanning lower-indexed processes
enter(self) ==
    /\ pc[self] = "enter"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ j' = [j EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]

\* Scan processes with lower indices
e2(self) ==
    /\ pc[self] = "e2"
    /\ IF j[self] < self
         THEN IF flag[j[self]]
                THEN /\ pc' = [pc EXCEPT ![self] = "e3"]
                     /\ UNCHANGED <<flag, j>>
                ELSE /\ j' = [j EXCEPT ![self] = j[self] + 1]
                     /\ UNCHANGED <<flag, pc>>
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
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED <<flag, j>>

\* Wait for all higher-indexed processes' flags to be lowered
e5(self) ==
    /\ pc[self] = "e5"
    /\ IF j[self] < N
         THEN /\ ~flag[j[self]]
              /\ j' = [j EXCEPT ![self] = j[self] + 1]
              /\ UNCHANGED <<flag, pc>>
         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED <<flag, j>>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<flag, j>>

\* Exit protocol: lower flag and reset index
exitCS(self) ==
    /\ pc[self] = "exit"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ j' = [j EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]

P(self) ==
    \/ ncs(self)
    \/ enter(self)
    \/ e2(self)
    \/ e3(self)
    \/ e4(self)
    \/ e5(self)
    \/ cs(self)
    \/ exitCS(self)

Next == \E self \in Procs : P(self)

Fairness ==
    \A self \in Procs :
        WF_vars(enter(self) \/ e2(self) \/ e3(self) \/ e4(self)
                \/ e5(self) \/ cs(self) \/ exitCS(self))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

=============================================================================
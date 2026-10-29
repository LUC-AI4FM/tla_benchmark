---------------------------- MODULE OneBitMutex ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 0 .. (N - 1)

VARIABLES x, pc, nxt

vars == << x, pc, nxt >>

Labels == {"ncs", "e1", "e2", "e3", "e4", "e5", "e6", "cs", "f"}

TypeOK ==
    /\ x \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> Labels]
    /\ nxt \in [Procs -> 0 .. N]

Init ==
    /\ x = [p \in Procs |-> FALSE]
    /\ pc = [p \in Procs |-> "ncs"]
    /\ nxt = [p \in Procs |-> 0]

\* Non-critical section: decide to try to enter
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, nxt >>

\* Raise own flag and start checking from process 0
E1(self) ==
    /\ pc[self] = "e1"
    /\ x' = [x EXCEPT ![self] = TRUE]
    /\ nxt' = [nxt EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "e2"]

\* Select the next process to check (in increasing order), skipping self
E2(self) ==
    /\ pc[self] = "e2"
    /\ IF nxt[self] = N
         THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED << x, nxt >>
         ELSE IF nxt[self] = self
                THEN /\ nxt' = [nxt EXCEPT ![self] = nxt[self] + 1]
                     /\ UNCHANGED << x, pc >>
                ELSE /\ pc' = [pc EXCEPT ![self] = "e3"]
                     /\ UNCHANGED << x, nxt >>

\* Read the flag of the process being checked
E3(self) ==
    /\ pc[self] = "e3"
    /\ IF x[nxt[self]]
         THEN /\ IF nxt[self] < self
                   THEN pc' = [pc EXCEPT ![self] = "e4"]
                   ELSE pc' = [pc EXCEPT ![self] = "e6"]
              /\ UNCHANGED << x, nxt >>
         ELSE /\ nxt' = [nxt EXCEPT ![self] = nxt[self] + 1]
              /\ pc' = [pc EXCEPT ![self] = "e2"]
              /\ UNCHANGED x

\* Lower-numbered conflict: back off by lowering own flag
E4(self) ==
    /\ pc[self] = "e4"
    /\ x' = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "e5"]
    /\ UNCHANGED nxt

\* Wait for the lower-numbered process to finish, then restart
E5(self) ==
    /\ pc[self] = "e5"
    /\ ~x[nxt[self]]
    /\ pc' = [pc EXCEPT ![self] = "e1"]
    /\ UNCHANGED << x, nxt >>

\* Higher-numbered conflict: wait for it to finish, then continue checking
E6(self) ==
    /\ pc[self] = "e6"
    /\ ~x[nxt[self]]
    /\ nxt' = [nxt EXCEPT ![self] = nxt[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "e2"]
    /\ UNCHANGED x

\* Critical section
CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "f"]
    /\ UNCHANGED << x, nxt >>

\* Exit protocol: clear own flag
F(self) ==
    /\ pc[self] = "f"
    /\ x' = [x EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED nxt

Trying(self) ==
    \/ E1(self) \/ E2(self) \/ E3(self) \/ E4(self)
    \/ E5(self) \/ E6(self) \/ CS(self) \/ F(self)

Proc(self) == NCS(self) \/ Trying(self)

Next == \E self \in Procs : Proc(self)

Fairness == \A self \in Procs : WF_vars(Trying(self))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Set of processes currently in their critical section
cs == {p \in Procs : pc[p] = "cs"}

InCS(p) == pc[p] = "cs"

MutualExclusion == \A i, j \in Procs : (i # j) => ~(InCS(i) /\ InCS(j))

Mutex == Cardinality(cs) <= 1

\* Deadlock freedom: if some process is trying, some process eventually enters CS
DeadlockFree ==
    (\E p \in Procs : pc[p] \in {"e1", "e2", "e3", "e4", "e5", "e6"})
        ~> (\E p \in Procs : pc[p] = "cs")

=============================================================================
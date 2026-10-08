---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N >= 2

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

ProcSet == {1} \cup (2..N)

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in 1..N |-> FALSE]
    /\ pc = [self \in ProcSet |-> "start"]

start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "write_x"]
    /\ UNCHANGED <<x, y>>

write_x(self) ==
    /\ pc[self] = "write_x"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "check_y"]
    /\ UNCHANGED <<y, b>>

check_y(self) ==
    /\ pc[self] = "check_y"
    /\ IF y /= 0
       THEN /\ pc' = [pc EXCEPT ![self] = "backoff"]
            /\ UNCHANGED <<x, y, b>>
       ELSE /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "verify_x"]
            /\ UNCHANGED <<x, b>>

backoff(self) ==
    /\ pc[self] = "backoff"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "wait_y"]
    /\ UNCHANGED <<x, y>>

wait_y(self) ==
    /\ pc[self] = "wait_y"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b>>

verify_x(self) ==
    /\ pc[self] = "verify_x"
    /\ IF x = self
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<x, y, b>>
       ELSE /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "scan_init"]
            /\ UNCHANGED <<x, y>>

scan_init(self) ==
    /\ pc[self] = "scan_init"
    /\ pc' = [pc EXCEPT ![self] = "scan"]
    /\ UNCHANGED <<x, y, b>>

scan(self) ==
    /\ pc[self] = "scan"
    /\ \A j \in 1..N : (j /= self) => (b[j] = FALSE)
    /\ pc' = [pc EXCEPT ![self] = "check_y_final"]
    /\ UNCHANGED <<x, y, b>>

check_y_final(self) ==
    /\ pc[self] = "check_y_final"
    /\ IF y = self
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "wait_y2"]
    /\ UNCHANGED <<x, y, b>>

wait_y2(self) ==
    /\ pc[self] = "wait_y2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b>>

cs(self) ==
    /\ pc[self] = "cs"
    /\ TRUE
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<x, y, b>>

exit(self) ==
    /\ pc[self] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x>>

proc1 ==
    \/ start(1)
    \/ write_x(1)
    \/ check_y(1)
    \/ backoff(1)
    \/ wait_y(1)
    \/ verify_x(1)
    \/ scan_init(1)
    \/ scan(1)
    \/ check_y_final(1)
    \/ wait_y2(1)
    \/ cs(1)
    \/ exit(1)

procN(self) ==
    \/ start(self)
    \/ write_x(self)
    \/ check_y(self)
    \/ backoff(self)
    \/ wait_y(self)
    \/ verify_x(self)
    \/ scan_init(self)
    \/ scan(self)
    \/ check_y_final(self)
    \/ wait_y2(self)
    \/ cs(self)
    \/ exit(self)

Next ==
    \/ proc1
    \/ \E self \in 2..N : procN(self)

Fairness ==
    /\ WF_vars(proc1)
    /\ \A self \in 2..N : WF_vars(procN(self))

Spec == Init /\ [][Next]_vars /\ Fairness

InCS(i) == pc[i] = "cs"

MutualExclusion ==
    \A i, j \in ProcSet : (i /= j) => ~(InCS(i) /\ InCS(j))

Invariant == MutualExclusion

Liveness == []<>(\E i \in ProcSet : InCS(i))

==========================================================================
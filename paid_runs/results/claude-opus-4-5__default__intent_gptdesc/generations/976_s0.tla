---------------------------- MODULE RingProcesses ----------------------------

EXTENDS Naturals

CONSTANTS N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES reg,      \* reg[i] is the shared register of process i
          result,   \* result[i] is where process i stores the read value
          pc        \* pc[i] is the program counter of process i

vars == <<reg, result, pc>>

Procs == 0..(N-1)

LeftNeighbor(i) == (i - 1 + N) % N

TypeOK ==
    /\ reg \in [Procs -> {0, 1}]
    /\ result \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"write", "read", "done"}]

Init ==
    /\ reg = [i \in Procs |-> 0]
    /\ result = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "write"]

Write(i) ==
    /\ pc[i] = "write"
    /\ reg' = [reg EXCEPT ![i] = 1]
    /\ result' = result
    /\ pc' = [pc EXCEPT ![i] = "read"]

Read(i) ==
    /\ pc[i] = "read"
    /\ result' = [result EXCEPT ![i] = reg[LeftNeighbor(i)]]
    /\ reg' = reg
    /\ pc' = [pc EXCEPT ![i] = "done"]

Step(i) ==
    \/ Write(i)
    \/ Read(i)

Next ==
    \/ \E i \in Procs : Step(i)
    \/ /\ \A i \in Procs : pc[i] = "done"
       /\ UNCHANGED vars

Fairness == \A i \in Procs : WF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

AllTerminated == \A i \in Procs : pc[i] = "done"

AtLeastOneResultIsOne == \E i \in Procs : result[i] = 1

Safety == AllTerminated => AtLeastOneResultIsOne

Termination == <>AllTerminated

LastWriter ==
    \E i \in Procs :
        /\ pc[i] = "read"
        /\ \A j \in Procs : j # i => pc[j] \in {"read", "done"}

InductiveInvariant ==
    /\ TypeOK
    /\ (\A i \in Procs : pc[i] \in {"read", "done"} => reg[i] = 1)
    /\ (AllTerminated => AtLeastOneResultIsOne)
    /\ ((\A i \in Procs : pc[i] \in {"read", "done"}) =>
        (\E i \in Procs : pc[i] = "read" \/ result[i] = 1))

=============================================================================
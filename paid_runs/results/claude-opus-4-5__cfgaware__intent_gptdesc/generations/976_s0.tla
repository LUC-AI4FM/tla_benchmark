---------------------------- MODULE RingProtocol ----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES reg, result, pc

vars == <<reg, result, pc>>

Procs == 0..(N-1)

LeftNeighbor(i) == (i + N - 1) % N

PCStates == {"ready", "written", "done"}

TypeOK ==
    /\ reg \in [Procs -> {0, 1}]
    /\ result \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> PCStates]

Init ==
    /\ reg = [i \in Procs |-> 0]
    /\ result = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "ready"]

Write(i) ==
    /\ pc[i] = "ready"
    /\ reg' = [reg EXCEPT ![i] = 1]
    /\ result' = result
    /\ pc' = [pc EXCEPT ![i] = "written"]

Read(i) ==
    /\ pc[i] = "written"
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

PCorrect == AllTerminated => AtLeastOneResultIsOne

Termination == <>(\A i \in Procs : pc[i] = "done")

SomeoneWrittenOrDone == \E i \in Procs : pc[i] \in {"written", "done"}

LastWriter == 
    \E i \in Procs : 
        /\ pc[i] \in {"written", "done"}
        /\ \A j \in Procs : (j # i /\ pc[j] = "done") => result[j] = 1

Inv ==
    /\ TypeOK
    /\ (AllTerminated => AtLeastOneResultIsOne)
    /\ (\E i \in Procs : pc[i] # "ready") => (\E i \in Procs : reg[i] = 1)

=============================================================================
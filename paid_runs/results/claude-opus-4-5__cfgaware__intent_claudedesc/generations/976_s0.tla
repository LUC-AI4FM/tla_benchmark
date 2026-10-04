-------------------------------- MODULE spec --------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLAPS

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLES pc, x, y

vars == <<pc, x, y>>

Procs == 0..(N-1)

Init ==
    /\ pc = [i \in Procs |-> "write"]
    /\ x = [i \in Procs |-> 0]
    /\ y = [i \in Procs |-> 0]

Write(i) ==
    /\ pc[i] = "write"
    /\ x' = [x EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "read"]
    /\ y' = y

Read(i) ==
    /\ pc[i] = "read"
    /\ y' = [y EXCEPT ![i] = x[(i - 1 + N) % N]]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ x' = x

Done(i) ==
    /\ pc[i] = "done"
    /\ UNCHANGED vars

Step(i) == Write(i) \/ Read(i) \/ Done(i)

Next == \E i \in Procs : Step(i)

Fairness == \A i \in Procs : WF_vars(Write(i)) /\ WF_vars(Read(i))

Spec == Init /\ [][Next]_vars /\ Fairness

AllDone == \A i \in Procs : pc[i] = "done"

AtLeastOneYIsOne == \E i \in Procs : y[i] = 1

PCorrect == AllDone => AtLeastOneYIsOne

TypeOK ==
    /\ pc \in [Procs -> {"write", "read", "done"}]
    /\ x \in [Procs -> {0, 1}]
    /\ y \in [Procs -> {0, 1}]

WrittenSet == {i \in Procs : x[i] = 1}

ReadSet == {i \in Procs : pc[i] = "done"}

InvHelper ==
    \A i \in Procs :
        /\ (pc[i] \in {"read", "done"} => x[i] = 1)
        /\ (y[i] = 1 => pc[i] = "done")

InvCircular ==
    \A i \in Procs :
        (pc[i] = "done" /\ x[(i - 1 + N) % N] = 1) => y[i] = 1

InvKey ==
    AllDone => 
        \E i \in Procs : 
            LET j == (i + 1) % N
            IN pc[j] = "done" /\ x[i] = 1

Inv ==
    /\ TypeOK
    /\ InvHelper
    /\ InvCircular
    /\ (\A i \in Procs : pc[i] # "write" => x[i] = 1)
    /\ (AllDone => AtLeastOneYIsOne)

Termination == <>AllDone

=============================================================================
---------------------------- MODULE RingRegisters ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 0 .. (N - 1)

Left(i) == (i + N - 1) % N

ControlStates == {"a", "b", "done"}

-----------------------------------------------------------------------------

TypeOK ==
    /\ x  \in [Procs -> {0, 1}]
    /\ y  \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> ControlStates]

Init ==
    /\ x  = [i \in Procs |-> 0]
    /\ y  = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "a"]

StepA(i) ==
    /\ pc[i] = "a"
    /\ x' = [x EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "b"]
    /\ UNCHANGED y

StepB(i) ==
    /\ pc[i] = "b"
    /\ y' = [y EXCEPT ![i] = x[Left(i)]]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED x

Proc(i) == StepA(i) \/ StepB(i)

AllDone == \A i \in Procs : pc[i] = "done"

Terminating ==
    /\ AllDone
    /\ UNCHANGED vars

Next ==
    \/ \E i \in Procs : Proc(i)
    \/ Terminating

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ \A i \in Procs : WF_vars(Proc(i))

-----------------------------------------------------------------------------

PCorrect == AllDone => \E i \in Procs : y[i] = 1

Inv ==
    /\ TypeOK
    /\ \A i \in Procs : pc[i] \in {"b", "done"} => x[i] = 1
    /\ PCorrect

Termination == <>AllDone

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM InductiveInvariant == Spec => []Inv

THEOREM Safety == Spec => []PCorrect

THEOREM Liveness == FairSpec => Termination

=============================================================================
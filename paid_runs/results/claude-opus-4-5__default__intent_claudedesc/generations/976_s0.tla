---------------------------- MODULE CircularProcesses ----------------------------
EXTENDS Integers, Naturals, TLAPS, FiniteSets

CONSTANTS N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES pc, x, y

vars == <<pc, y, x>>

Procs == 0..(N-1)

TypeOK ==
    /\ pc \in [Procs -> {"s1", "s2", "done"}]
    /\ x \in [Procs -> {0, 1}]
    /\ y \in [Procs -> {0, 1}]

Init ==
    /\ pc = [i \in Procs |-> "s1"]
    /\ x = [i \in Procs |-> 0]
    /\ y = [i \in Procs |-> 0]

LeftNeighbor(i) == (i - 1 + N) % N

Step1(i) ==
    /\ pc[i] = "s1"
    /\ x' = [x EXCEPT ![i] = 1]
    /\ pc' = [pc EXCEPT ![i] = "s2"]
    /\ y' = y

Step2(i) ==
    /\ pc[i] = "s2"
    /\ y' = [y EXCEPT ![i] = x[LeftNeighbor(i)]]
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ x' = x

Next ==
    \E i \in Procs : Step1(i) \/ Step2(i)

AllTerminated == \A i \in Procs : pc[i] = "done"

AtLeastOneRead1 == \E i \in Procs : y[i] = 1

Postcondition == AllTerminated => AtLeastOneRead1

Fairness == \A i \in Procs : WF_vars(Step1(i)) /\ WF_vars(Step2(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Liveness == <>AllTerminated

WrittenSet == {i \in Procs : x[i] = 1}

NotYetReadSet == {i \in Procs : pc[i] # "done"}

InductiveInvariant ==
    /\ TypeOK
    /\ \A i \in Procs : (pc[i] # "s1") => (x[i] = 1)
    /\ \A i \in Procs : (pc[i] = "done" /\ y[i] = 1) => TRUE
    /\ (AllTerminated => AtLeastOneRead1)
    /\ (NotYetReadSet # {} \/ AtLeastOneRead1)
    /\ \A i \in Procs : pc[i] = "done" => (y[i] = 1 \/ x[LeftNeighbor(i)] = 0)

StrongerInductive ==
    /\ TypeOK
    /\ \A i \in Procs : pc[i] \in {"s2", "done"} => x[i] = 1
    /\ \A i \in Procs : (pc[i] = "done" /\ y[i] = 0) => 
         (pc[LeftNeighbor(i)] = "s1" /\ x[LeftNeighbor(i)] = 0)
    /\ ~(\A i \in Procs : pc[i] = "done" /\ y[i] = 0)

ChainInvariant ==
    /\ TypeOK
    /\ \A i \in Procs : pc[i] # "s1" => x[i] = 1
    /\ \A i \in Procs : y[i] = 1 => x[LeftNeighbor(i)] = 1
    /\ \A i \in Procs : (pc[i] = "done" /\ y[i] = 0) => pc[LeftNeighbor(i)] = "s1"
    /\ ~(AllTerminated /\ \A i \in Procs : y[i] = 0)

THEOREM InitEstablishesTypeOK == Init => TypeOK
    BY NAssumption DEF Init, TypeOK, Procs

THEOREM TypeOKPreserved == TypeOK /\ Next => TypeOK'
    BY NAssumption DEF TypeOK, Next, Step1, Step2, Procs, LeftNeighbor

THEOREM InvariantImpliesPostcondition == 
    StrongerInductive => Postcondition
    BY DEF StrongerInductive, Postcondition, AllTerminated, AtLeastOneRead1, TypeOK, Procs

SafetyProperty == []Postcondition

THEOREM Spec => SafetyProperty
    PROOF OMITTED

THEOREM Spec => Liveness
    PROOF OMITTED

=============================================================================
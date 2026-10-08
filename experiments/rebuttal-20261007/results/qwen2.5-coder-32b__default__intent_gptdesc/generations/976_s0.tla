------------------------------- MODULE RingProcesses -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES reg, res, state \* reg: local shared registers, res: result registers, state: control states

\* Control states: 0 = before first step, 1 = between steps, 2 = terminated
Init == 
    /\ reg = [p \in 1..N -> 0]
    /\ res = [p \in 1..N -> 0]
    /\ state = [p \in 1..N -> 0]

Next ==
    \/ \E p \in 1..N : state[p] = 0 /\ 
        (/\ reg' = [reg EXCEPT ![p] = 1]
         /\ res' = res
         /\ state' = [state EXCEPT ![p] = 1])
    \/ \E p \in 1..N : state[p] = 1 /\
        (/\ reg' = reg
         /\ res' = [res EXCEPT ![p] = reg[IF p = 1 THEN N ELSE p - 1]]
         /\ state' = [state EXCEPT ![p] = 2])

Spec ==
    /\ Init
    /\ [][Next]_<<reg, res, state>>
    /\ WF_next(<<reg, res, state>>)

\* Safety invariants
TypeInvariant ==
    /\ \A p \in 1..N : reg[p] \in {0, 1}
    /\ \A p \in 1..N : res[p] \in {0, 1}
    /\ \A p \in 1..N : state[p] \in {0, 1, 2}

SafetyProperty ==
    (\A p \in 1..N : state[p] = 2) => (\E p \in 1..N : res[p] = 1)

\* Liveness property
TerminationLiveness ==
    <>(\A p \in 1..N : state[p] = 2)

Invariant ==
    TypeInvariant /\ SafetyProperty

THEOREM Spec => []Invariant

=============================================================================
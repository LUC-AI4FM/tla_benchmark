------------------------------- MODULE CircleAlgorithm -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES array1, array2, states

Init == 
    /\ array1 = <<0>> ^ N
    /\ array2 = <<0>> ^ N
    /\ states = [p \in 0..N-1 |-> "init"]

Next ==
    \/ \E p \in 0..N-1 : states[p] = "init" /\ 
        (array1' = [array1 EXCEPT ![p] = 1]
         /\ array2' = array2
         /\ states' = [states EXCEPT ![p] = "write"])
    \/ \E p \in 0..N-1 : states[p] = "write" /\
        (array1' = array1
         /\ array2' = [array2 EXCEPT ![p] = array1[(p - 1) % N]]
         /\ states' = [states EXCEPT ![p] = "done"])

Spec ==
    /\ Init
    /\ [][Next]_<<array1, array2, states>>
    /\ <><\A p \in 0..N-1 : states[p] = "done">>_<<array1, array2, states>>

SafetyInvariant ==
    \A s \in States : 
        (\A p \in 0..N-1 : s.states[p] = "done") => 
            (\E q \in 0..N-1 : s.array2[q] = 1)

InductiveInvariant ==
    \A s \in States :
        /\ \A p \in 0..N-1 : s.states[p] \in {"init", "write", "done"}
        /\ \A p \in 0..N-1 : s.states[p] = "done" => s.array2[p] \in {0, 1}
        /\ (\E p \in 0..N-1 : s.states[p] = "write") => 
            (\E q \in 0..N-1 : s.array1[q] = 1)

TypeInvariant ==
    /\ array1 \in [0..N-1 -> {0, 1}]
    /\ array2 \in [0..N-1 -> {0, 1}]
    /\ states \in [0..N-1 -> {"init", "write", "done"}]

THEOREM Spec => []TypeInvariant
THEOREM Spec => []InductiveInvariant
THEOREM Spec => []SafetyInvariant

=============================================================================
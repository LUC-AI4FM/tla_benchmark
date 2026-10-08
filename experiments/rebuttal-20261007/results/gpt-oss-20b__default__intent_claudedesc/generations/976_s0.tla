------------------------------ MODULE SimpleConcurrent ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N \in Nat

VARIABLES arr1, arr2, procState

vars == {arr1, arr2, procState}

Init ==
    /\ arr1 = [i \in 0..N-1 |-> 0]
    /\ arr2 = [i \in 0..N-1 |-> 0]
    /\ procState = [i \in 0..N-1 |-> 0]

Step1(i) ==
    /\ i \in 0..N-1
    /\ procState[i] = 0
    /\ arr1' = [arr1 EXCEPT ![i] = 1]
    /\ procState' = [procState EXCEPT ![i] = 1]
    /\ arr2' = arr2

Step2(i) ==
    /\ i \in 0..N-1
    /\ procState[i] = 1
    /\ let left == (i - 1) mod N in
       arr2' = [arr2 EXCEPT ![i] = arr1[left]]
    /\ procState' = [procState EXCEPT ![i] = 2]
    /\ arr1' = arr1

Next ==
    ∃ i \in 0..N-1 : (Step1(i) \/ Step2(i))

AllDone == ∀ i \in 0..N-1 : procState[i] = 2

Inv ==
    /\ arr1 \in [0..N-1 -> {0,1}]
    /\ arr2 \in [0..N-1 -> {0,1}]
    /\ procState \in [0..N-1 -> {0,1,2}]
    /\ ∀ i \in 0..N-1 :
        (procState[i] = 0 => arr1[i] = 0 /\ arr2[i] = 0)
      /\ (procState[i] = 1 => arr1[i] = 1 /\ arr2[i] = 0)
      /\ (procState[i] = 2 => arr1[i] = 1 /\ arr2[i] = arr1[(i - 1) mod N])

Spec ==
    Init /\ [][Next]_vars

SafetyInvariant == Inv /\ (AllDone => ∃ i \in 0..N-1 : arr2[i] = 1)

LivenessProperty == ∀ i \in 0..N-1 : []<> (procState[i] = 2)

THEOREM Safety_Inv_Is_Invariant: []Inv
THEOREM Postcondition_Holds: []SafetyInvariant
THEOREM Termination: LivenessProperty

------------------------------ END MODULE ------------------------------
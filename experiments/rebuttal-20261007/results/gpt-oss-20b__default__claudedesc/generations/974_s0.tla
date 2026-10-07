------------------------------ MODULE RegularRegisters ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N \* number of processes

VARIABLES x, y, state

(* Type invariants *)
TypeOK == /\ x \in [0..N-1 -> SUBSET {0,1} \ {∅}]
          /\ y \in [0..N-1 -> {0,1}]
          /\ state \in [0..N-1 -> {"a1","a2","b","Done"}]

(* Initial condition *)
Init == /\ TypeOK
        /\ ∀ i \in 0..N-1 : x[i] = {0}
        /\ ∀ i \in 0..N-1 : y[i] = 0
        /\ ∀ i \in 0..N-1 : state[i] = "a1"

(* Actions for each process *)
A1(i) == /\ state[i] = "a1"
          /\ x' = [x EXCEPT ![i] = {0,1}]
          /\ state' = [state EXCEPT ![i] = "a2"]
          /\ y' = y

A2(i) == /\ state[i] = "a2"
          /\ x' = [x EXCEPT ![i] = {1}]
          /\ state' = [state EXCEPT ![i] = "b"]
          /\ y' = y

B(i) ==
  LET prev == Mod(i - 1, N) IN
  /\ state[i] = "b"
     /\ y' = [y EXCEPT ![i] = CHOOSE v ∈ x[prev] : TRUE]
     /\ state' = [state EXCEPT ![i] = "Done"]
     /\ x' = x

Stutter == UNCHANGED <<x, y, state>>

Next ==
  ∃ i \in 0..N-1 :
    (A1(i) \/ A2(i) \/ B(i))
  \/ Stutter

(* Structural conditions for invariant *)
WriteCompleted ==
  ∀ i \in 0..N-1 : (state[i] = "b" \/ state[i] = "Done") => x[i] = {1}

NotAllDoneOrSomeYOne ==
  (∃ i \in 0..N-1 : state[i] # "Done")
  \/ (∃ i \in 0..N-1 : y[i] = 1)

Inv == TypeOK /\ WriteCompleted /\ NotAllDoneOrSomeYOne

(* Safety property *)
PCorrect ==
  (∀ i \in 0..N-1 : state[i] = "Done") => (∃ i \in 0..N-1 : y[i] = 1)

(* Liveness property: all processes eventually finish *)
Termination == <> (∀ i \in 0..N-1 : state[i] = "Done")

Spec == Init /\ [][Next]_<<x, y, state>> /\ Termination

=============================================================================
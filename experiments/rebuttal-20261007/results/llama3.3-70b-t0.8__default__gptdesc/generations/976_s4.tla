```
MODULE RingAlgorithm
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, pc

Init ==
  /\ x = [i \in 1..N |-> 0]
  /\ y = [i \in 1..N |-> 0]
  /\ pc = [i \in 1..N |-> "start"]

Next ==
  \/ \E i \in 1..N :
      /\ pc[i] = "start"
      /\ x' = [x EXCEPT ![i] = 1]
      /\ y' = y
      /\ pc' = [pc EXCEPT ![i] = "copy"]
  \/ \E i \in 1..N :
      /\ pc[i] = "copy"
      /\ x' = x
      /\ y' = [y EXCEPT ![i] = x[(i-1 # N) + 1]]
      /\ pc' = [pc EXCEPT ![i] = "done"]
  \/ \E i \in 1..N :
      /\ pc[i] = "done"
      /\ UNCHANGED <<x, y, pc>>

Spec == Init /\ [][Next]_<<x, y, pc>>
Termination == <>(\A i \in 1..N : pc[i] = "done")

SafetyProperty == []<>(\E i \in 1..N : y[i] = 1)

Inv == /\ x \in [1..N -> Nat]
      /\ y \in [1..N -> Nat]
      /\ pc \in [1..N -> {"start", "copy", "done"}]

THEOREM Termination => []<>SafetyProperty
PROOF * TLS proof *
  <1>1. Termination
    BY DEF Termination
  <1>2. Inv
    SUFFICE TO PROVE Inv
      INVARIANCE THEOREM
      BY DEF Inv
      CASE Next
        <2>1. \E i : pc[i] = "start"
          x' = [x EXCEPT ![i] = 1]
            THEN UNSUBST x'
              x \in [1..N -> Nat]
                BY <2>1
        <2>2. \E i : pc[i] = "copy"
          y' = [y EXCEPT ![i] = x[(i-1 # N) + 1]]
            THEN UNSUBST y'
              y \in [1..N -> Nat]
                BY <2>2
        <2>3. \E i : pc[i] = "done"
          UNCHANGED <<x, y, pc>>
            THEN UNSUBST pc'
              pc \in [1..N -> {"start", "copy", "done"}]
                BY <2>3
  <1>3. []<>SafetyProperty
    PROOF * TLS proof *
      <3>1. Termination => []<>(\A i : pc[i] = "done")
        LTL THEOREM
        BY DEF Termination
      <3>2. (\A i : pc[i] = "done") => SafetyProperty
        PROOF * TLS proof *
          <4>1. \A i : pc[i] = "done"
            SUFFICE TO PROVE SafetyProperty
              LTL THEOREM
              BY DEF SafetyProperty
```

Note: The `* TLS proof *` parts are placeholders for actual TLAPS proofs that would be generated using the TLAPS tool.
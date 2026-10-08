#### Github790.tla
```
MODULE Github790

EXTENDS Integers

CONSTANTS 

VARIABLES a

Init == (a = 0)

Next == (a' = a)

Spec == Init /\ [][Next]_a

AlwaysTrue == <>TRUE => <>[]TRUE

THEOREM Spec => AlwaysTrue
```

#### Github790_proof.tla
```
MODULE Github790_proof

EXTENDS Github790, TLAPS

PROOF THEOREM Spec => AlwaysTrue
  <1>1. Assume ~Spec
    BY CONTRADICATION
  <2>2. SUFFICES ASSUME NEW s \in Spec
    BY DEF Spec
  <3>3. QED
    BY <2>
```
Note: This output is in TLA+ syntax and includes the necessary components as requested, but keep in mind that the `THEOREM` statement in `Github790.tla` does not include a proof and is meant to be used with a model checker or theorem prover. The actual proof of the theorem would typically involve additional steps and possibly the use of tools like TLAPS for formal verification, as indicated in the second module.
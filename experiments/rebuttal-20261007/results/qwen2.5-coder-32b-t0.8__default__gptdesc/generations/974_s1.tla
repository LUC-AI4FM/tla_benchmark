```tla
MODULE SharedMemoryAlgorithm

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N \* Number of processes

VARIABLES x, y, done

Init == 
  /\ x = <<{0} \: i \in 1..N>>
  /\ y = <<0 \: i \in 1..N>>
  /\ done = {FALSE \: i \in 1..N}

Next ==
  \/ \E i \in 1..N \: 
     \/\ /\ ~done[i]
        /\ x' = [x EXCEPT ![i] = x[i] \cup {1}]
        /\ y' = y
        /\ done' = done
     \\/ /\ ~done[i]
        /\ x'[i] = {1}
        /\ y'[i] = CHOOSE v \in x[(i % N) + 1]: TRUE
        /\ done'[i] = TRUE
        /\ x'' = [x' EXCEPT ![i] = {y'[i]}]
        /\ y'' = y'
        /\ done'' = done'

Spec ==
  WF_vars(Init, Next, UNCHANGED <<x, y, done>>, {vars \in SUBSET {[1..N] -> BOOLEAN} : vars /= {}})
  /\ SpecFair

SpecFair == 
  WF_vars(Init, Next, UNCHANGED <<x, y, done>>, {vars \in SUBSET {[1..N] -> BOOLEAN} : vars = {}})

Termination ==
  \A i \in 1..N : done[i]

PCorrect ==
  Termination => (\E i \in 1..N : y[i] = 1)

Inv ==
  /\ \A i \in 1..N : x[i] /= {}
  /\ \A i \in 1..N : (done[i] => y[i] \in {0, 1})
  
Spec =>
  <>[] Inv
  /\ []<> Termination
  /\ [] PCorrect
```

```tlaps

THEOREM Spec => [] PCorrect
<1> SUFFICES ASSUME NEW /\ Spec OBVIOUS
    <2>1 SUFFICES PROVE INV /\ (Termination => (\E i \in 1..N : y[i] = 1)) BY DEF Inv, Termination, PCorrect
        <3> CASE ~ Termination
            <4> QED
        <3> CASE Termination
            <4> SUFFICES PROVE (\E i \in 1..N : y[i] = 1) OBVIOUS
                <5> USE CHOOSE_EXISTS DEF x, done
                    <6> QED

THEOREM Spec => [] Inv
<1> BY PREDICATE_NORMALIZATION WITH Spec AS <<P>>, Init AS <<I>>, Next AS <<N>> THEN DEF PCorrect
<2> BY INVARIANTS_WITH_CONTRACTS "<>"
    <3> SUFFICES PROVE I /\ [](N /\ (UNCHANGED <<x, y, done>>) => UNCHANGED Inv) OBVIOUS
        <4> <5> SUFFICES ASSUME NEW /\ I /\ N
                <6>1 SUFFICES PROVE INV /\ UNCHANGED Inv BY DEF Inv
                    <7> QED

```
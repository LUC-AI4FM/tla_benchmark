```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES sem, pc

Init ==
  /\ sem = <<1, 1, ..., 1>>  \* N copies of 1
  /\ pc = <<-1, -1, ..., -1>>  \* N copies of -1

Next ==
  \/ \E i \in 0..N-1 :
    IF pc[i] = -1 THEN
      /\ sem' = [sem EXCEPT ![i] = 0]
      /\ pc' = [pc EXCEPT ![i] = 0]
      /\ OTHERS ==<<>>
    ELSE IF pc[i] = 0 THEN
      IF i = 0 THEN
        /\ sem' = [sem EXCEPT ![(i+1) % N] = 0]
        /\ pc' = [pc EXCEPT ![i] = 1]
        /\ OTHERS ==<<>>
      ELSE
        /\ sem' = [sem EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![i] = 1]
        /\ OTHERS ==<<>>
    ELSE IF pc[i] = 1 THEN
      /\ sem' = [sem EXCEPT ![i] = 1, ![(i+1) % N] = 1]
      /\ pc' = [pc EXCEPT ![i] = -1]
      /\ OTHERS ==<<>>
    ELSE
      FALSE

Spec ==
  /\ Init
  /\ [][Next]_sem
  /\ WF_vars(Next, sem)

Inv ==
  \A i \in 0..N-2 : pc[i] # 1 \/ pc[(i+1) % N] # 1

StarvationFreedom ==
  \A i \in 0..N-1 : <>[]<>(pc[i] = 1)

THEOREM Spec => []Inv
THEOREM Spec => StarvationFreedom
```
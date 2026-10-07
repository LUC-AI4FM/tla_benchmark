```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES sem, pc

Init ==
  /\ sem = [i \in 0..N-1 |-> 1]
  /\ pc = [i \in 0..N-1 |-> "think"]

Next ==
  \/ \E i \in 0..N-1 :
    IF pc[i] = "think"
    THEN
      IF i = 0
      THEN
        /\ sem[N-1] = 1
        /\ sem' = [sem EXCEPT ![N-1] = 0]
        /\ pc' = [pc EXCEPT ![i] = "left_fork"]
        /\ UNCHANGED <<sem, pc>>
      ELSE
        /\ sem[i] = 1
        /\ sem' = [sem EXCEPT ![i] = 0]
        /\ pc' = [pc EXCEPT ![i] = "right_fork"]
        /\ UNCHANGED <<sem, pc>>
    ELSE IF pc[i] = "left_fork"
    THEN
      IF i = 0
      THEN
        /\ sem[0] = 1
        /\ sem' = [sem EXCEPT ![0] = 0]
        /\ pc' = [pc EXCEPT ![i] = "eat"]
        /\ UNCHANGED <<sem, pc>>
      ELSE
        /\ sem[(i-1) mod N] = 1
        /\ sem' = [sem EXCEPT ![(i-1) mod N] = 0]
        /\ pc' = [pc EXCEPT ![i] = "eat"]
        /\ UNCHANGED <<sem, pc>>
    ELSE IF pc[i] = "right_fork"
    THEN
      /\ sem[(i-1) mod N] = 1
      /\ sem' = [sem EXCEPT ![(i-1) mod N] = 0]
      /\ pc' = [pc EXCEPT ![i] = "eat"]
      /\ UNCHANGED <<sem, pc>>
    ELSE IF pc[i] = "eat"
    THEN
      /\ sem[i] = 0
      /\ sem[(i-1) mod N] = 0
      /\ sem' = [sem EXCEPT ![i] = 1, ![(i-1) mod N] = 1]
      /\ pc' = [pc EXCEPT ![i] = "think"]
      /\ UNCHANGED <<sem, pc>>

Invariant ==
  \A i \in 0..N-2 : ~(pc[i] = "eat" /\ pc[i+1] = "eat")

Spec ==
  /\ Init
  /\ [][Next]_<<sem, pc>>
  /\ WF_vars(Next, <<sem, pc>>)

StarvationFree ==
  \A i \in 0..N-1 : <>[]<>(pc[i] = "eat")
```
Note: The `UNCHANGED` operator is used to specify that the values of some variables do not change in a given step. However, since TLA+ requires all variables to be specified when using `UNCHANGED`, we use `UNCHANGED <<sem, pc>>` to indicate that only the `pc` and `sem` variables are being considered for change, even though other variables may exist in the system (none do in this case). 

Also note that TLA+ does not have a direct equivalent of "strong fairness" as described in some process algebra or temporal logic formalisms. Instead, we use the `WF_vars` operator to specify weak fairness for each variable, which is sufficient for ensuring liveness properties like freedom from starvation in this context.
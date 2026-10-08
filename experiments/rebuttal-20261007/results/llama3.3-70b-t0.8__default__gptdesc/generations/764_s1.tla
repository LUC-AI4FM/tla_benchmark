```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES sem, pc

Init ==
  /\ sem = <<1, 1, ..., 1>>  \* Initialize all forks as available
  /\ pc = [i \in 0..N-1 |-> "thinking"]  \* All philosophers are thinking initially

Next ==
  \/ \E i \in 0..N-1 :
      IF pc[i] = "thinking" THEN
        /\ sem' = sem
        /\ pc' = [pc EXCEPT ![i] = "hungry"]
      ELSE IF pc[i] = "hungry" THEN
        IF i = 0 THEN
          /\ sem' = [sem EXCEPT ![(i + N - 1) % N] = 0]
          /\ pc' = [pc EXCEPT ![i] = "eating"]
        ELSE
          /\ sem' = [sem EXCEPT ![i] = 0]
          /\ pc' = [pc EXCEPT ![i] = "waitright"]
        ENDIF
      ELSE IF pc[i] = "waitright" THEN
        /\ sem' = [sem EXCEPT ![(i + 1) % N] = 0]
        /\ pc' = [pc EXCEPT ![i] = "eating"]
      ELSE IF pc[i] = "eating" THEN
        /\ sem' = [sem EXCEPT ![i] = 1]
        /\ pc' = [pc EXCEPT ![i] = "thinking"]
      ENDIF

Spec == Init /\ [][Next]_<<sem, pc>>
Fairness == \A i \in 0..N-1 : WF(Next, pc[i])

Inv == \A i \in 0..N-1 :
        ~(pc[i] = "eating" /\ pc[(i + 1) % N] = "eating")

StarvationFreedom == \A i \in 0..N-1 :
                     <>[]<>(pc[i] = "eating")
```
Note: The above specification assumes that the `sem` variable is a sequence of length `N`, where each element represents the availability of a fork. A value of 1 indicates that the fork is available, and 0 indicates that it is not. The `pc` variable is an array of length `N`, where each element represents the control state of a philosopher. The values "thinking", "hungry", "waitright", and "eating" represent the different states that a philosopher can be in.

Also note that this specification uses the `EXCEPT` operator to create a new function by modifying an existing one, which is a common idiom in TLA+. It also uses the `\A` and `\E` quantifiers to express universal and existential quantification, respectively. The `WF` predicate is used to express weak fairness, which ensures that every philosopher gets a chance to make progress if they are enabled infinitely often.
--------------------------- MODULE DiningPhilosophers ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE sem, pc

sem == <<>> \* a sequence of booleans representing fork availability
pc == [i \in 0..N-1 |-> "thinking"] \* control-state variable for each philosopher

Init ==
  /\ sem = [i \in 0..N-1 |-> TRUE] \* all forks available initially
  /\ pc = [i \in 0..N-1 |-> "thinking"]

Philosopher(i) == 
  IF pc[i] = "thinking" THEN 
    IF i # 0 THEN \* philosophers 1 through N-1 acquire right fork first
      /\ sem' = [sem EXCEPT ![i] = FALSE]
      /\ pc' = [pc EXCEPT ![i] = "hungryR"]
    ELSE \* philosopher 0 acquires left fork first
      /\ sem' = [sem EXCEPT ![(i+1) % N] = FALSE]
      /\ pc' = [pc EXCEPT ![i] = "hungryL"]
  ELSE IF pc[i] = "hungryR" THEN 
    /\ sem' = [sem EXCEPT ![(i+1) % N] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "eating"]
  ELSE IF pc[i] = "hungryL" THEN 
    /\ sem' = [sem EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "eating"]
  ELSE IF pc[i] = "eating" THEN 
    /\ sem' = [sem EXCEPT ![i] = TRUE]
    /\ sem' = [sem' EXCEPT ![(i+1) % N] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "thinking"]
  ELSE FALSE

Next ==
  \/ \E i \in 0..N-1 : Philosopher(i)

Spec == 
  Init /\ [][Next]_<<sem, pc>>
  
Fairness == 
  \A i \in 0..N-1 : WF_Var(Philosopher(i), <<sem, pc>>)
  
Invariant == 
  \A i \in 0..N-1 : ~(pc[i] = "eating" /\ pc[(i+1) % N] = "eating")
  
StarvationFreedom == 
  \A i \in 0..N-1 : []<>pc[i] = "eating"
===============================================================================
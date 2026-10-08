---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE sem, pc

Var == <<sem, pc>>

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
          /\ sem[(i-1) % N] = 1
          /\ sem' = [sem EXCEPT ![(i-1) % N] = 0]
          /\ pc' = [pc EXCEPT ![i] = "eat"]
          /\ UNCHANGED <<sem, pc>>
      ELSE IF pc[i] = "right_fork"
      THEN
        /\ sem[(i-1) % N] = 1
        /\ sem' = [sem EXCEPT ![(i-1) % N] = 0]
        /\ pc' = [pc EXCEPT ![i] = "eat"]
        /\ UNCHANGED <<sem, pc>>
      ELSE IF pc[i] = "eat"
      THEN
        /\ sem[i] = 0
        /\ sem' = [sem EXCEPT ![i] = 1]
        /\ IF i = 0
          THEN /\ sem[N-1] = 0
               /\ sem' = [sem' EXCEPT ![N-1] = 1]
          ELSE /\ sem[(i-1) % N] = 0
               /\ sem' = [sem' EXCEPT ![(i-1) % N] = 1]
        /\ pc' = [pc EXCEPT ![i] = "think"]
        /\ UNCHANGED <<sem, pc>>
  \/ \E i \in 0..N-1 :
      IF pc[i] = "eat"
      THEN
        /\ sem[i] = 0
        /\ sem' = [sem EXCEPT ![i] = 1]
        /\ IF i = 0
          THEN /\ sem[N-1] = 0
               /\ sem' = [sem' EXCEPT ![N-1] = 1]
          ELSE /\ sem[(i-1) % N] = 0
               /\ sem' = [sem' EXCEPT ![(i-1) % N] = 1]
        /\ pc' = [pc EXCEPT ![i] = "think"]
        /\ UNCHANGED <<sem, pc>>

Spec ==
  /\ Init
  /\ [][Next]_Var
  /\ WF_Var(Next)

Invariant ==
  \A i, j \in 0..N-1 :
    \/ pc[i] # "eat"
    \/ pc[j] # "eat"
    \/ i = j

StarvationFree ==
  \A i \in 0..N-1 :
    <<pc[i] = "eat">>~

=============================================================================
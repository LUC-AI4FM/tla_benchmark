```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets
CONSTANTS N
VARIABLES sem, pc

Init ==
  /\ sem = [i \in 0..N-1 |-> 1]
  /\ pc = [i \in 0..N-1 |-> IF i = 0 THEN "l01" ELSE "l1"]

Next ==
  \/ \E i \in 0..N-1 :
    IF i = 0
    THEN
      CASE pc[i] OF
        "l01" => /\ sem[i] = 1
                 /\ sem' = [sem EXCEPT ![i] = 0]
                 /\ pc' = [pc EXCEPT ![i] = "l02"]
                 /\ UNCHANGED <<sem, pc>>
        "l02" => /\ sem[(i+1) % N] = 1
                 /\ sem' = [sem EXCEPT ![(i+1) % N] = 0]
                 /\ pc' = [pc EXCEPT ![i] = "l03"]
                 /\ UNCHANGED <<sem, pc>>
        "l03" => /\ pc' = [pc EXCEPT ![i] = "l04"]
                 /\ UNCHANGED sem
                 /\ UNCHANGED <<sem, pc>>
        "l04" => /\ sem[i] = 0
                 /\ sem' = [sem EXCEPT ![i] = 1]
                 /\ pc' = [pc EXCEPT ![i] = "l01"]
                 /\ UNCHANGED <<sem, pc>>
      ELSE
        CASE pc[i] OF
          "l1" => /\ sem[(i+1) % N] = 1
                   /\ sem' = [sem EXCEPT ![(i+1) % N] = 0]
                   /\ pc' = [pc EXCEPT ![i] = "l2"]
                   /\ UNCHANGED <<sem, pc>>
          "l2" => /\ sem[i] = 1
                   /\ sem' = [sem EXCEPT ![i] = 0]
                   /\ pc' = [pc EXCEPT ![i] = "l3"]
                   /\ UNCHANGED <<sem, pc>>
          "l3" => /\ pc' = [pc EXCEPT ![i] = "l4"]
                   /\ UNCHANGED sem
                   /\ UNCHANGED <<sem, pc>>
          "l4" => /\ sem[(i+1) % N] = 0
                   /\ sem' = [sem EXCEPT ![(i+1) % N] = 1]
                   /\ pc' = [pc EXCEPT ![i] = "l1"]
                   /\ UNCHANGED <<sem, pc>>
      END

Invariant ==
  \A i \in 0..N-2 : pc[i] # "l03" \/ pc[i+1] # "l03"
  /\ (pc[0] # "l03") \/ (pc[N-1] # "l03")

Spec == Init /\ [][Next]_<<sem, pc>>
       /\ \A i \in 0..N-1 : WF_vars(Next, <<sem, pc>>, i)

StarvationFree == \A i \in 0..N-1 : []<>pc[i] = "l03"

THEOREM Spec => []Invariant
THEOREM Spec => StarvationFree

```
Note: To check the model with N = 4, you would instantiate the constant `N` to be 4 when running the model checker.
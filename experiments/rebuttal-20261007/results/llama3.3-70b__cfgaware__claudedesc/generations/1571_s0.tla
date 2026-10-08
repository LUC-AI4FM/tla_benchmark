---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE sem, pc

sem == <<1 >> \* N
pc == [i \in 0..N-1 |-> IF i = 0 THEN "l01" ELSE "l1"]

Invariant ==
  /\ sem \in [0..N-1 -> {0, 1}]
  /\ pc \in [0..N-1 -> {"l1", "l2", "l3", "l4", "l01", "l02", "l03", "l04"}]
  /\ \A i \in 0..N-1 : 
    \/ pc[i] = "l1"
    \/ pc[i] = "l2"
    \/ pc[i] = "l3"
    \/ pc[i] = "l4"
    \/ pc[i] = "l01"
    \/ pc[i] = "l02"
    \/ pc[i] = "l03"
    \/ pc[i] = "l04"

TypeOK ==
  /\ sem \in [0..N-1 -> {0, 1}]
  /\ pc \in [0..N-1 -> {"l1", "l2", "l3", "l4", "l01", "l02", "l03", "l04"}]

Next ==
  \E i \in 0..N-1 :
    IF i = 0 THEN
      CASE pc[i] = "l01" /\ sem[0] = 1 ->
          sem' = [sem EXCEPT ![0] = 0];
          pc' = [pc EXCEPT ![i] = "l02"]
      [] pc[i] = "l02" /\ sem[1] = 1 ->
          sem' = [sem EXCEPT ![1] = 0];
          pc' = [pc EXCEPT ![i] = "l03"]
      [] pc[i] = "l03" ->
          pc' = [pc EXCEPT ![i] = "l04"];
          sem' = sem
      [] pc[i] = "l04" ->
          sem' = [sem EXCEPT ![0] = 1];
          pc' = [pc EXCEPT ![i] = "l01"]
      ELSE
        CASE pc[i] = "l1" /\ sem[(i+1) % N] = 1 ->
            sem' = [sem EXCEPT ![(i+1) % N] = 0];
            pc' = [pc EXCEPT ![i] = "l2"]
        [] pc[i] = "l2" /\ sem[i] = 1 ->
            sem' = [sem EXCEPT ![i] = 0];
            pc' = [pc EXCEPT ![i] = "l3"]
        [] pc[i] = "l3" ->
            pc' = [pc EXCEPT ![i] = "l4"];
            sem' = sem
        [] pc[i] = "l4" ->
            sem' = [sem EXCEPT ![(i+1) % N] = 1];
            pc' = [pc EXCEPT ![i] = "l1"]
        ELSE
          sem' = sem;
          pc' = pc
    END
  END

Spec ==
  /\ Init
  /\ [][Next]_<<sem, pc>>
  /\ \A i \in 0..N-1 : WF(Next, <<sem, pc>>)

StarvationFree ==
  \A i \in 0..N-1 :
    <>[]<>(pc[i] = "l3" \/ (i = 0 /\ pc[i] = "l03"))

THEOREM Spec => []Invariant
THEOREM Spec => StarvationFree

Init ==
  /\ sem = <<1 >> \* N
  /\ pc = [i \in 0..N-1 |-> IF i = 0 THEN "l01" ELSE "l1"]
===============================================================================
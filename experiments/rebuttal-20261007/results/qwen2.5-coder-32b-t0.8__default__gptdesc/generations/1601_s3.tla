---- MODULE FischerTimedMutex ----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, Delta, Epsilon, Infinity

VARIABLES timer, queue, cs, in_cs

Init == /\ timer \in [1..N -> {0}]
        /\ queue = << >>
        /\ cs \in [1..N -> FALSE]
        /\ in_cs = FALSE

Next ==
  \/ \E i \in 1..N :
      /\ ~cs[i]
      /\ ~in_cs
      /\ timer[i] = 0
      /\ ~(\E j \in queue: timer[j] < timer[i])
      /\ (queue = << >> \/ (\A j \in queue: timer[j] >= timer[i]))
      /\ /\ cs' = [cs EXCEPT ![i] = TRUE]
         /\ in_cs' = TRUE
         /\ queue' = Append(queue, i)
         /\ timer' = [timer EXCEPT ![i] = Infinity]
  \/ \E i \in 1..N :
      /\ cs[i]
      /\ in_cs
      /\ queue = <<i>>
      /\ /\ cs' = [cs EXCEPT ![i] = FALSE]
         /\ in_cs' = FALSE
         /\ queue' = << >>
         /\ timer' = timer
  \/ \E i \in 1..N :
      /\ ~cs[i]
      /\ timer[i] /= 0
      /\ /\ cs' = cs
         /\ in_cs' = in_cs
         /\ queue' = queue
         /\ timer' = [timer EXCEPT ![i] = IF timer[i] > Delta THEN timer[i] - Delta ELSE 0]
  \/ \E i \in 1..N :
      /\ ~cs[i]
      /\ timer[i] /= 0
      /\ in_cs
      /\ queue # << >>
      /\ queue[1] # i
      /\ /\ cs' = cs
         /\ in_cs' = in_cs
         /\ queue' = queue
         /\ timer' = [timer EXCEPT ![i] = IF timer[i] > Epsilon THEN timer[i] - Epsilon ELSE 0]

Spec ==
  /\ Init
  /\ [][Next]_<<timer, queue, cs, in_cs>>
  /\ <>(\E i \in 1..N: cs[i])

MutualExclusion == [](cs \notin {TRUE} \/ cs = [i \in 1..N |-> FALSE])

Invariant ==
  /\ MutualExclusion

Fairness ==
  WFQueue(<<timer, queue, cs, in_cs>>, queue)

THEOREM Spec => []Invariant
THEOREM Spec => Fairness

====
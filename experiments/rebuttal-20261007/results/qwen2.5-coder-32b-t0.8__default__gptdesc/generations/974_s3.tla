------------------------------ MODULE SharedMemoryAlgorithm ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N

VARIABLES x, y, done

Init == 
  /\ x = <<{0} \o i \in 1..N>> 
  /\ y = <<0 \o i \in 1..N>>
  /\ done = { }

Next ==
  \/ \E i \in 1..N \ (i \notin done) /\ 
     (x' = [x EXCEPT ![i] = x[i] \cup {1}] 
      /\ y' = y
      /\ done' = done)
  \/ \E i \in 1..N \ (i \notin done) /\ 
     (x'[i] = x[i]
      /\ y'[i] = CHOOSE v \in x[IF i = 1 THEN N ELSE i-1]: TRUE
      /\ done' = done \cup {i})

Spec ==
  Init /\ [][Next]_<<x, y, done>>

PCorrect == 
  /\ \A i \in 1..N: i \in done
  /\ \E i \in 1..N: y[i] = 1

Inv ==
  /\ \A i \in 1..N: x[i] \subseteq {0, 1}
  /\ \A i \in 1..N: (i \notin done) => (x[i] = {0} \/ x[i] = {0, 1})
  /\ \A i \in 1..N: (i \in done) => (x[i] = {1})

THEOREM PCorrect
    <1> SUFFICES ASSUME Inv
                PROVE PCorrect
    OBVIOUS

THEOREM Inv
    <1> SUFFICES ASSUME Init, \A k \in 0.. Len(<<Next>>): [][Next]_<<x,y,done>> => Inv'
    PROVE INVARIANT Inv
    BY DEF Next
    QED

=============================================================================
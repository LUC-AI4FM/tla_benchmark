------------------------------- MODULE LockProtocol -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N \* Number of processes

VARIABLES h_turn, s, turn, choosing, lock_held

Init == /\ h_turn = << >>
        /\ s = 0
        /\ turn = 0
        /\ choosing = [i \in 1..N -> FALSE]
        /\ lock_held = [i \in 1..N -> FALSE]

Next ==
    \/ \/ \E i \in 1..N : 
           /\ choosing[i]
           /\ s = 0
           /\ turn = (CHOOSE t \in 1..N \ {i} : TRUE)
           /\ h_turn' = Append(h_turn, <<i, turn>>)
           /\ s' = 1
           /\ UNCHANGED <<choosing, lock_held>>
       \/ /\ choosing[i]
          /\ s = 1
          /\ \A j \in 1..N \ {i} : ~choosing[j] \/ (j < i /\ turn = j)
          /\ s' = 2
          /\ UNCHANGED <<h_turn, choosing, lock_held>>
       \/ /\ choosing[i]
          /\ s = 2
          /\ lock_held' = [lock_held EXCEPT ![i] = TRUE]
          /\ choosing' = [choosing EXCEPT ![i] = FALSE]
          /\ s' = 0
          /\ UNCHANGED <<h_turn, turn>>
       \/ \/ \E i \in 1..N :
              /\ lock_held[i]
              /\ lock_held' = [lock_held EXCEPT ![i] = FALSE]
              /\ UNCHANGED <<h_turn, choosing, s, turn>>

Spec == Init /\ [][Next]_<<h_turn, s, turn, choosing, lock_held>>

Inv ==
    /\ \A i \in 1..N : \/ ~choosing[i] \/ (s > 0)
    /\ \A i \in 1..N : \/ ~lock_held[i] \/ (choosing[i] = FALSE)

Fairness ==
    WF_next(choosing)

=============================================================================
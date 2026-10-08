---------------------------- MODULE Barrier --------------------------------
EXTENDS Integers

CONSTANT N

VARIABLES state

Spec == Initialize /\ [][Next]_state

Initialize == (* Initial condition: all processes are approaching *)
            state = [i \in 1..N |-> "approaching"]

Next == (* The next step for each process *)
       \/ \E i \in 1..N :
          (* A process arrives at the barrier *)
          (state[i] = "approaching") /\ 
          (state' = [state EXCEPT ![i] = "arrived"])
       \/ \A i \in 1..N :
          (* All processes have arrived, reset the barrier *)
          (state[i] = "arrived") /\
          (state' = [i \in 1..N |-> "approaching"])

TypeOK == (* Type invariant: each process is in one of its two valid states *)
         \A i \in 1..N : state[i] \in {"approaching", "arrived"}

BarrierProperty == (* Stuttering-tolerant action property: no premature releases *)
                   \A i \in 1..N :
                     <<state[i] = "arrived">>_{state} 
                     >> ([\A j \in 1..N : state[j] = "arrived"]_{state})

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty

=============================================================================
---- MODULE SharedMemoryAlgorithm ----

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS N \* Number of processes

VARIABLES x, y, done

Init == 
    /\ x = <<{0} \: i \in 1..N>>
    /\ y = <<0 \: i \in 1..N>>
    /\ done = {FALSE \: i \in 1..N}

Next ==
    \/ /\ E\<exists>\<i \in 1..N\> (done[i] = FALSE)
       /\ \/ /\ x[i] = {x[i][1]}
          /\ x' = [x EXCEPT ![i] = {x[i][1], 1}]
          /\ UNCHANGED <<y, done>>
       \/ /\ x[i] = {x[i][1], 1}
          /\ x' = [x EXCEPT ![i] = {1}]
          /\ y' = [y EXCEPT ![i % N + 1] = 1]
          /\ done' = [done EXCEPT ![i] = TRUE]
          /\ UNCHANGED <<x, y[EXCEPT ![i % N + 1]]>>
    \/ UNCHANGED <<x, y, done>>

Spec ==
    Init /\ [][Next]_<<x,y,done>> /\ WF_(Next)_<<x,y,done>>

PCorrect == 
    (\A i \in 1..N : done[i]) => (\E i \in 1..N : y[i] = 1)

Inv ==
    (\A i \in 1..N : (done[i] => y[i] = 1))

THEOREM Spec => [](PCorrect)

PROOF PCorrect
    <|
        SUFFICES ASSUME NEW /\ Spec
                 PROVE  PCorrect
        OBVIOUS
    >>

LEMMA Inv \*<<x,y,done>>
    <|
        BY PFOLDR(Next, Inv, Init)
            DEF Inv, Next, Init, Spec
    >>

THEOREM Spec => []Inv
    <|
        SUFFICES ASSUME NEW /\ Spec
                 PROVE  []Inv
        OBVIOUS
    >>

====
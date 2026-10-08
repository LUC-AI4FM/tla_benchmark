------------------------------- MODULE SharedMemoryAlgorithm -------------------------------

EXTENDS Naturals, TLC, FiniteSets

CONSTANTS N

VARIABLES x, y, done

Init == /\ x = <<{0} \ {j \in 1..N : j /= i} >>_i \in 1..N
        /\ y = <<0>>_i \in 1..N
        /\ done = FALSE

Next ==
    LET ChooseProcess == CHOOSE p \in (1..N) \ {p' \in 1..N : done[p']} :
                          UNCHANGED <<x, y>> EXCEPT ![p] := x[p] \cup {1}
                                      /\ UNCHANGED <<y>> EXCEPT ![p] := CHOOSE v \in x[(p+1) % N + 1] : TRUE
                                      /\ UNCHANGED done
        WriteAndRead == \E p \in (1..N) \ {p' \in 1..N : done[p']} :
                          \/ /\ x'[p] = x[p] \cup {1}
                             /\ y'[p] \in x[(p+1) % N + 1]
                             /\ done' = done EXCEPT ![p] := TRUE
                          \/ ChooseProcess
    IN WriteAndRead

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, done>>
    /\ <>(\A i \in 1..N : done[i]) => (\E j \in 1..N : y[j] = 1))_<<x, y, done>>

Inv ==
    \A i \in 1..N :
        \/ ~done[i]
        \/ (y[i] = 1)

THEOREM Spec => [](Inv)
<1>1. PCorrect:   ASSUME NEW /\ Spec
                      PROVE  <>(\A i \in 1..N : done[i]) => (\E j \in 1..N : y[j] = 1))
<1>2. InvInductive: ASSUME NEW /\ Spec /\ Init /\ [][Next]_<<x, y, done>> /\ Inv
                      PROVE  [](Inv)

================================================================================
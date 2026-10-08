------------------------------- MODULE TokenRing --------------------------------
EXTENDS Naturals

CONSTANTS N, M
ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ N >= 1
       /\ M >= 1
       /\ N <= M + 1

VARIABLES values

Init == \/ N = 1 /\ values = <<0>>
        \/ /\ N > 1 
           /\ values \in [0..N-1 -> 0..M-1]
           /\ (\E i \in 0..N-2 : values[i] # values[i+1])
           /\ values[N-1] # values[0]

Next == \/ /\ values = <<0>>
            /\ UNCHANGED values
        \/ /\ E \subseteq [0..N-1 -> BOOLEAN]
           /\ (\A i \in 0..N-1 : E[i] => 
                   (i = 0 /\ values[i]' = (values[N-1] + 1) % M)
                 \/ (i > 0 /\ values[i]' = values[i-1]))
           /\ (\A i \in [0..N-1] \ E : values[i]' = values[i])

Spec == Init /\ [][Next]_<<values>>

SafetyInvariant ==
    [](\E i \in 0..N-1 : \A j \in (i+1)..(i+N-2)%N : values[i] # values[j])

Stabilization ==
    <>(\E v \in 0..M-1 : 
        [](values = <<v>> \/ (\A i \in 1..N-1 : values[i] = values[i-1])))

WF == WF_next(<<values>>)

FairNext == \A E \subseteq [0..N-1 -> BOOLEAN] : Next => <>E

===============================================================================
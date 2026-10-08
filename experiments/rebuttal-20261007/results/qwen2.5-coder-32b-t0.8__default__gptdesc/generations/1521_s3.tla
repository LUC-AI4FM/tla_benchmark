------------------------------ MODULE CoffeeCan ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS MaxBeanCount

VARIABLES Beans

(* --algorithm CoffeeCan

variables black = 0, white = 0;

Init == /\ black \in 0..MaxBeanCount
        /\ white \in 0..MaxBeanCount
        /\ black + white <= MaxBeanCount
        /\ Beans = [BLACK |-> black, WHITE |-> white]

Next ==
    \/ /\ Beans[BLACK] >= 2
       /\ 'Beans' = [Beans EXCEPT ![BLACK] = Beans[BLACK] - 2]
    \/ /\ Beans[WHITE] >= 2
       /\ 'Beans' = [Beans EXCEPT ![WHITE] = Beans[WHITE] - 2]
    \/ /\ Beans[BLACK] >= 1
       /\ Beans[WHITE] >= 1
       /\ 'Beans' = [Beans EXCEPT ![BLACK] = Beans[BLACK] - 1, ![WHITE] = Beans[WHITE] - 1]
    \/ /\ Beans[BLACK] + Beans[WHITE] = 1
       /\ 'Beans' = Beans

Spec == Init /\ [][Next]_<<Beans>>

TypeInvariant ==
    /\ Beans[BLACK] \in Integers
    /\ Beans[WHITE] \in Integers
    /\ Beans[BLACK] >= 0
    /\ Beans[WHITE] >= 0
    /\ Beans[BLACK] + Beans[WHITE] <= MaxBeanCount

MonotonicDecrease ==
    /\ TypeInvariant
    /\ (/\ OLD(Beans)[BLACK] > Beans[BLACK]
        \/ OLD(Beans)[WHITE] > Beans[WHITE])

Termination ==
    <>[]Beans[BLACK] + Beans[WHITE] = 1

ParityInvariant ==
    /\ TypeInvariant
    /\ (Beans[WHITE] % 2 = OLD(Beans)[WHITE] % 2)

FinalBeanColor ==
    <>(/\ Beans[BLACK] + Beans[WHITE] = 1
        /\ (Beans[WHITE] = 0 <=> OLD(Beans)[WHITE] % 2 = 1))

WF_spec == WF_vars(Next, <<Beans>>)

=============================================================================
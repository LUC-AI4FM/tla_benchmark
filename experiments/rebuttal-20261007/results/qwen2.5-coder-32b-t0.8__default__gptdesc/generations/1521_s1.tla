------------------------------- MODULE CoffeeCanBeanProblem -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS MaxBeans
VARIABLES beans

Init == /\ TypeOK
        /\ beans.black \in 0..MaxBeans
        /\ beans.white \in 0..MaxBeans
        /\ beans.black + beans.white > 0

TypeOK == \/ beans = <<beans.black, beans.white>>
          \/ FALSE

Next ==
    \/ /\ beans.black >= 2
       /\ beans' = <<beans.black - 2, beans.white>>    
    \/ /\ beans.white >= 2
       /\ beans' = <<beans.black, beans.white - 2>> 
    \/ /\ beans.black >= 1
       /\ beans.white >= 1  
       /\ beans' = <<beans.black - 1, beans.white - 1>>
    \/ /\ beans.black + beans.white = 1
       /\ beans' = <<beans.black, beans.white>>

Spec == Init /\ [][Next]_<<beans>>

TotalBeansDecreasing ==
    \A b \in SUBSET States : 
        /\ b # {}
        /\ (/\ s \in b : s.beans.black + s.beans.white > 0)
        => (\E s1, s2 \in b : s1 << beans < s2 << beans)

Termination ==
    <>[]<>(beans.black + beans.white = 1)

ParityInvariant ==
    \A b \in SUBSET States :
        /\ b # {}
        /\ (/\ s \in b : s.beans.black + s.beans.white > 1)
        => (\E s \in b : EVEN(s.beans.white) <=> EVEN(beans.white))

FinalBeanColor ==
    <>[]<>(beans.black + beans.white = 1) =>
        (beans.white = 1 <=> EVEN(beans.white))

Liveness == WeakFairness(Next)

=============================================================================
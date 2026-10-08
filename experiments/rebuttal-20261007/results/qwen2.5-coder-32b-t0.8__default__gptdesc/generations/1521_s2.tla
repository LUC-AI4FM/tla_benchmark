---------------------------- MODULE CoffeeCanBeanProblem ----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxBeans

VARIABLES beans

Init == /\beans = [black |-> 0, white |-> 0]
      /\ beans.black + beans.white <= MaxBeans

Next ==
    \/ \/ beans.black >= 2
       /\ \E newBeans \in SUBSET [black |-> 0..MaxBeans, white |-> 0..MaxBeans] :
          \/ /\ beans' = [beans EXCEPT ![black] = beans.black - 2, ![white] = beans.white]
             /\ newBeans = beans'
       \/ /\ beans' = [beans EXCEPT ![black] = beans.black - 1, ![white] = beans.white - 1]
          /\ newBeans = beans'
    \/ \/ beans.white >= 2
       /\ \E newBeans \in SUBSET [black |-> 0..MaxBeans, white |-> 0..MaxBeans] :
          \/ /\ beans' = [beans EXCEPT ![black] = beans.black - 1, ![white] = beans.white]
             /\ newBeans = beans'
       \/ /\ beans' = [beans EXCEPT ![black] = beans.black, ![white] = beans.white - 2]
          /\ newBeans = beans'
    \/ \/ beans.black + beans.white = 1
       /\ beans' = beans

Spec ==
    /\ Init
    /\ [][Next]_<<beans>>
    /\ WF_next(<<beans>>)

TypeInvariant == /\ beans.black \in 0..MaxBeans
                 /\ beans.white \in 0..MaxBeans

MonotonicDecrease == \A s, t \in State: s << t => (s.beans.black + s.beans.white) >= (t.beans.black + t.beans.white)

Termination ==
    <>(beans.black = 1 \/ beans.white = 1)

ParityInvariant ==
    [](beans.black + beans.white > 1 => (beans.white % 2 = Init.beans.white % 2))

FinalBeanHypothesis ==
    <>(beans.black = 1 /\ Init.beans.white % 2 = 1) \/ (beans.white = 1 /\ Init.beans.white % 2 = 0)

=============================================================================
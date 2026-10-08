MODULE RingTermination
EXTENDS Naturals, FiniteSets

CONSTANT N, K
NodeSet == 1..N

VARIABLES active, pend, detected

BoundedPend == ∀ i ∈ NodeSet : pend[i] <= K

Terminate(i) ==
    /\ i ∈ NodeSet
    /\ active[i]
    /\ pend[i] = 0
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<pend, detected>>

SendMessage(sender, receiver) ==
    /\ sender ∈ NodeSet
    /\ receiver ∈ NodeSet
    /\ sender # receiver
    /\ active[sender]
    /\ pend[receiver] < K
    /\ pend' = [pend EXCEPT ![receiver] = @ + 1]
    /\ UNCHANGED <<active, detected>>

ReceiveMessage(i) ==
    /\ i ∈ NodeSet
    /\ pend[i] > 0
    /\ pend' = [pend EXCEPT ![i] = @ - 1]
    /\ UNCHANGED <<active, detected>>

DetectTermination ==
    /\ active = [i \in NodeSet |-> FALSE]
    /\ pend = [i \in NodeSet |-> 0]
    /\ detected' = TRUE
    /\ UNCHANGED <<active, pend>>

TerminateAct == ∃ i ∈ NodeSet : Terminate(i)
SendAct      == ∃ sender, receiver ∈ NodeSet : SendMessage(sender, receiver)
ReceiveAct   == ∃ i ∈ NodeSet : ReceiveMessage(i)

Next == TerminateAct \/ SendAct \/ ReceiveAct \/ DetectTermination

Init ==
    /\ active = [i \in NodeSet |-> TRUE]
    /\ pend = [i \in NodeSet |-> 0]
    /\ detected = FALSE
    /\ BoundedPend

DetectedImplyTermination ==
    [] (detected => ∀ i ∈ NodeSet : active[i] = FALSE /\ pend[i] = 0)

TerminationStable ==
    [] (detected => detected')

Terminated == ∀ i ∈ NodeSet : active[i] = FALSE /\ pend[i] = 0

Liveness == WF_vars(DetectTermination) /\ []( Terminated => <> detected)

Spec == Init /\ [][Next]_(active, pend, detected) /\ [] BoundedPend
        /\ DetectedImplyTermination /\ TerminationStable /\ Liveness

END MODULE
------------------------------- MODULE HuangTermination -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Procs, Leader, MaxDenominator \* Procs is a finite set of processes, Leader is in Procs, MaxDenominator is a natural number

VARIABLES weights, messages, active

Init == /\ weights = [p \in Procs |-> 0]
        /\ messages = {}
        /\ active = {Leader}
        /\ weights[Leader] = 1

WeightMsg(p, q, w) == <<p, q, w>>

Next ==
    \/ \E p \in active : \E q \in (Procs \ {p}) :
            /\ q \notin active
            /\ messages' = messages \cup {WeightMsg(p, q, weights[p])}
            /\ weights' = [weights EXCEPT ![p] = 0]
            /\ active' = active \ {p}
    \/ \E p \in (Procs \ active) :
            /\ messages' = messages
            /\ weights' = weights
            /\ active' = active \cup {p}
    \/ \E msg \in messages : 
            LET <<sender, receiver, weight>> == msg IN
            /\ receiver \in active
            /\ messages' = messages \ {msg}
            /\ weights' = [weights EXCEPT ![receiver] = weights[receiver] + weight]
            /\ active' = active

Spec ==
    /\ Init
    /\ [][Next]_<<active, messages>>
    /\ WF_next(<<active, messages>>)

InvariantTotalWeight ==
    \A s \in StateSpace : Sum({weights[p] : p \in Procs}) + Sum({msg[2] : msg \in messages}) = 1

InvariantNoNegativeWeights ==
    \A s \in StateSpace : \A p \in Procs : weights[p] >= 0

InvariantWeightFractions ==
    \A s \in StateSpace : \A p \in Procs : weights[p] = n \div d => /\ n \in Nat
                                                            /\ d \in 1..MaxDenominator
                                                            /\ n <= d

InvariantNoMessagesWhenTerminated ==
    \A s \in StateSpace :
        \/ active[Leader] \/ messages /= {} 
        \/ (\A p \in Procs : p \notin active)

LivenessTerminationDetected ==
    <>(/\ active = {}
         /\ messages = {}
         /\ weights[Leader] = 1)

SpecWithProperties ==
    Spec
    /\ []InvariantTotalWeight
    /\ []InvariantNoNegativeWeights
    /\ []InvariantWeightFractions
    /\ <>InvariantNoMessagesWhenTerminated

=============================================================================
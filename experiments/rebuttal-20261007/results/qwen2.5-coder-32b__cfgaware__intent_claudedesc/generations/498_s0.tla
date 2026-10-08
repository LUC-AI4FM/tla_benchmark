------------------------------- MODULE LiveSpec -------------------------------

CONSTANTS Values, Slots

VARIABLES proposals, choices

ASSUME CHOOSE v \in Values : TRUE \* Ensure Values is nonempty
ASSUME CHOOSE s \in Slots : TRUE   \* Ensure Slots is nonempty

Init == /\ proposals = {}
        /\ choices = [s \in Slots |-> <<>>]

Propose(v, s) == 
    /\ v \in Values
    /\ s \in Slots
    /\ \/ choices[s] = <<>>
       \/ choices[s] = <<proposals[s][1]>>
    /\ proposals' = [proposals EXCEPT ![s] = Append(proposals[s], v)]
    /\ UNCHANGED choices

Choose(s) ==
    /\ s \in Slots
    /\ choices[s] = <<>>
    /\ proposals[s] /= <<>>
    /\ \/ Len(proposals[s]) = 1
       \/ \E i \in 1..Len(proposals[s]) : 
            \A j \in 1..Len(proposals[s]) : proposals[s][i] = proposals[s][j]
    /\ choices' = [choices EXCEPT ![s] = <<Head(proposals[s])>>]
    /\ UNCHANGED proposals

Next == \/ \E v \in Values, s \in Slots : Propose(v, s)
        \/ \E s \in Slots : Choose(s)

Spec == Init /\ [][Next]_<<proposals, choices>>

TypeInvariant ==
    /\ proposals \in [Slots -> Seq(Values)]
    /\ choices \in [Slots -> Seq(Values)]

Nontriviality ==
    \A s \in Slots :
        choices[s] /= <<>> => \E v \in Values : v \in proposals[s]

Stability ==
    \A s \in Slots, v \in Values :
        choices[s] = <<v>> => \A t \in [0..Len(proposals[s])] : proposals[s][t] = v

Consistency ==
    \A s \in Slots :
        Len(choices[s]) <= 1

Liveness ==
    WF_next(Next) /\
    \A s \in Slots : <>[](choices[s] /= <<>>)

THEOREM Spec => []TypeInvariant
THEOREM Spec => [](Nontriviality)
THEOREM Spec => [](Stability)
THEOREM Spec => [](Consistency)
THEOREM Spec => <>(Liveness)

=============================================================================
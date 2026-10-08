------------------------------- MODULE LockProtocol -------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS N \* Number of processes

VARIABLES turn, h_turn, s, requesting, granted

Init == /\ turn = 0
        /\ h_turn = << >>
        /\ s = 0
        /\ requesting = {}
        /\ granted = {}

Next ==
    \/ /\ s = 0
       /\ \E i \in 1..N : requesting' = {i}
       /\ granted' = {}
       /\ turn' = turn
       /\ h_turn' = h_turn
       /\ s' = 1
    \/ /\ s = 1
       /\ requesting /= {}
       /\ \E i \in requesting : turn' = i
       /\ h_turn' = Append(h_turn, <<i>>)
       /\ granted' = {turn'}
       /\ requesting' = requesting \ {turn'}
       /\ s' = 2
    \/ /\ s = 2
       /\ granted /= {}
       /\ turn' = turn
       /\ h_turn' = h_turn
       /\ requesting' = requesting
       /\ granted' = {}
       /\ s' = 0

Spec == Init /\ [][Next]_<<requesting, granted, turn, h_turn, s>>

\* Safety invariants
TypeOK ==
    /\ turn \in 1..N \/ turn = 0
    /\ h_turn \in Seq(1..N)
    /\ s \in {0, 1, 2}
    /\ requesting \subseteq (1..N)
    /\ granted \subseteq (1..N)

MutualExclusion == Cardinality(granted) <= 1

NoStarvation ==
    \/ requesting = {}
    \/ \A i \in requesting : \E j \in 1..N :
         h_turn = << >> \/ Last(h_turn) = <<j>> /\ j = i

\* Liveness properties
Progress == <>[](\E i \in 1..N : requesting' = {i} => <><<>(granted = {i}))_<<requesting, granted>>

Fairness ==
    WF_next(<<requesting, granted, turn, h_turn, s>>)

=============================================================================
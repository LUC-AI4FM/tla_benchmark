------------------------------- MODULE LockProtocol -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N \* Number of processes

VARIABLES turn, h_turn, s, requesting, granted

Init == /\ turn = 0
        /\ h_turn = << >>
        /\ s = 0
        /\ requesting = {}
        /\ granted = {}

Next ==
    \/ \/ \E i \in (1..N) : 
            /\ i \notin requesting
            /\ i \notin granted
            /\ requesting' = requesting \cup {i}
            /\ UNCHANGED <<turn, h_turn, s, granted>>
       \/ \/ \E i \in requesting :
                /\ i = turn
                /\ s' = 1
                /\ UNCHANGED <<requesting, turn, h_turn, granted>>
           \/ \E i \in requesting :
                    /\ s = 1
                    /\ s' = 2
                    /\ UNCHANGED <<requesting, turn, h_turn, granted>>
               \/ \E i \in requesting :
                        /\ s = 2
                        /\ granted' = {i}
                        /\ requesting' = {}
                        /\ s' = 0
                        /\ UNCHANGED <<turn, h_turn>>
           \/ \E i \notin requesting :
                    /\ i = turn
                    /\ s = 0
                    /\ turn' = (turn % N) + 1
                    /\ h_turn' = Append(h_turn, turn)
                    /\ UNCHANGED <<requesting, granted, s>>
       \/ \/ \E i \in granted :
                /\ granted' = {}
                /\ turn' = (turn % N) + 1
                /\ h_turn' = Append(h_turn, turn)
                /\ UNCHANGED <<requesting, s>>

Spec == Init /\ [][Next]_<<turn, h_turn, s, requesting, granted>>

TypeInvariant ==
    /\ turn \in 1..N
    /\ h_turn \in Seq(1..N)
    /\ s \in {0, 1, 2}
    /\ requesting \subseteq (1..N)
    /\ granted \subseteq (1..N)

MutualExclusion == \/ granted = {}
                    \/ Cardinality(granted) = 1

SafetyInvariant ==
    TypeInvariant
    /\ MutualExclusion

LivenessProperty ==
    \A i \in 1..N :
        <>(\E t \in SUBSEQ(h_turn) : Last(t) = i)

Fairness ==
    WF_next(<<requesting, turn, h_turn, s, granted>>)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => LivenessProperty

=============================================================================
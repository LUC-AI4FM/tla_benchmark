------------------------------- MODULE LockProtocol -------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS N

VARIABLES turn, h_turn, s, requesting, critical, released

Init == /\ turn = 0 
        /\ h_turn = << >> 
        /\ s = FALSE 
        /\ requesting = {}
        /\ critical = {}
        /\ released = {}

Next == \/ \E i \in {1..N} : 
                /\ requesting' = requesting \cup {i}
                /\ critical' = critical
                /\ released' = released
                /\ h_turn' = h_turn
                /\ s' = FALSE
           \/ \E i \in {1..N} : 
                /\ requesting' = requesting \ {i}
                /\ critical' = critical \cup {i}
                /\ released' = released
                /\ h_turn' = Append(h_turn, <<i>>)
                /\ s' = TRUE
           \/ \E i \in {1..N} : 
                /\ requesting' = requesting
                /\ critical' = critical \ {i}
                /\ released' = released \cup {i}
                /\ h_turn' = h_turn
                /\ s' = FALSE

Spec == Init /\ [][Next]_<<requesting, critical, released, turn, h_turn, s>>

INV1 == \/ requesting = {}
         \/ \E i \in requesting : critical = {} /\ released = {}

INV2 == \A i \in {1..N} : critical \cap (critical \ {i}) = {}

Inv == INV1 /\ INV2

Liveness == <>[](\E i \in {1..N}: <>\<requesting' = requesting \cup {i}>)

Fairness == WF_next(Next)

=============================================================================
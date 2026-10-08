------------------------------- MODULE LockProtocol -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES lock, turn, h_turn, s, request

Init == /\ lock = FALSE 
        /\ turn \in 0..N-1 
        /\ h_turn = << >> 
        /\ s = 0 
        /\ request \in SUBSET (0..N-1)

Next == \/ /\ request /= {} 
              /\ \E i \in request: 
                   /\ lock = FALSE 
                   /\ turn = i 
                   /\ h_turn' = Append(h_turn, <<i, s>>)
                   /\ s' = s + 1
                   /\ lock' = TRUE 
                   /\ request' = {}
           \/ /\ lock = TRUE 
              /\ \E i \in (0..N-1) \ {turn}: 
                   /\ turn' = i 
                   /\ h_turn' = Append(h_turn, <<i, s>>)
                   /\ s' = s + 1
           \/ /\ lock = FALSE 
              /\ request /= {} 
              /\ \A i \in request: i /= turn 
              /\ h_turn' = Append(h_turn, <<turn, s>>)
              /\ s' = s + 1

Spec == /\ Init
        /\ [][Next]_<<lock, turn, h_turn, s, request>>
        /\ WF_next(<<lock, turn, h_turn, s, request>>)

Inv1 == \/ lock = FALSE 
          \/ \A i \in (0..N-1): 
               (\E j : h_turn[j][2] < s) => h_turn[j][1] /= turn

Inv2 == /\ request = {}
        \/ \A i \notin request: \E j : h_turn[j][1] = i => h_turn[j][2] < s

SpecFair == Spec /\ SF_\<<lock, turn, h_turn, s, request>>_request
=============================================================================
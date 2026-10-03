---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals

CONSTANTS N, K

ASSUME NAssumption == N > 0
ASSUME KAssumption == K > N

VARIABLES x, pc

vars == <<x, pc>>

Procs == 0..(N-1)

\* Process i holds a token if:
\* - For process 0: its value equals the value of the last process (N-1)
\* - For other processes: its value differs from its predecessor
HasToken(i) == IF i = 0 
               THEN x[i] = x[N-1]
               ELSE x[i] # x[i-1]

\* Count the number of token holders
TokenCount == Cardinality({i \in Procs : HasToken(i)})

\* At least one process holds a token
SomeoneHoldsToken == \E i \in Procs : HasToken(i)

\* Exactly one process holds a token
ExactlyOneHoldsToken == Cardinality({i \in Procs : HasToken(i)}) = 1

\* Eventually exactly one process holds a token (and it stays that way)
EventuallyJustOneHoldsToken == <>[](ExactlyOneHoldsToken)

\* Cardinality helper using recursive definition for finite sets
RECURSIVE SetCardinality(_)
SetCardinality(S) == IF S = {} THEN 0 ELSE 1 + SetCardinality(S \ {CHOOSE s \in S : TRUE})

Cardinality(S) == SetCardinality(S)

\* Initial state: all processes start at label "a"
\* x can be any value in 0..(K-1) for each process
Init == /\ x \in [Procs -> 0..(K-1)]
        /\ pc = [self \in Procs |-> "a"]

\* Process 0's action
P0(self) == /\ self = 0
            /\ pc[self] = "a"
            /\ IF x[0] = x[N-1]
               THEN x' = [x EXCEPT ![0] = (x[0] + 1) % K]
               ELSE x' = x
            /\ pc' = [pc EXCEPT ![self] = "a"]

\* Other processes' action (processes 1 to N-1)
POther(self) == /\ self \in 1..(N-1)
                /\ pc[self] = "a"
                /\ IF x[self] # x[self - 1]
                   THEN x' = [x EXCEPT ![self] = x[self - 1]]
                   ELSE x' = x
                /\ pc' = [pc EXCEPT ![self] = "a"]

\* Next state relation
Next == \E self \in Procs : P0(self) \/ POther(self)

\* Weak fairness for each process
Fairness == /\ WF_vars(P0(0))
            /\ \A self \in 1..(N-1) : WF_vars(POther(self))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Type invariant
TypeOK == /\ x \in [Procs -> 0..(K-1)]
          /\ pc \in [Procs -> {"a"}]

\* Safety property: someone always holds a token
Safety == SomeoneHoldsToken

\* Liveness property: eventually exactly one token holder
Liveness == EventuallyJustOneHoldsToken

\* Theorem: The specification satisfies both safety and liveness
THEOREM Spec => [](SomeoneHoldsToken) /\ EventuallyJustOneHoldsToken

=================================================================================
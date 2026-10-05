---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Integers, Naturals

CONSTANTS K, N

ASSUME NPositive == N > 0
ASSUME KGreaterThanN == K > N

VARIABLES x

vars == <<x>>

TypeOK == x \in [0..(N-1) -> 0..(K-1)]

\* Process 0 has a token if its value equals the value of the last process
HasToken0 == x[0] = x[N-1]

\* Process i (for i > 0) has a token if its value differs from its predecessor
HasTokenI(i) == x[i] # x[i-1]

\* General predicate: process i has a token
HasToken(i) == IF i = 0 THEN HasToken0 ELSE HasTokenI(i)

\* Count the number of token holders
TokenCount == Cardinality({i \in 0..(N-1) : HasToken(i)})

\* The set of processes that currently hold a token
TokenHolders == {i \in 0..(N-1) : HasToken(i)}

\* Helper: cardinality for finite sets
Cardinality(S) == 
    LET Card[T \in SUBSET S] == 
        IF T = {} THEN 0
        ELSE LET elem == CHOOSE e \in T : TRUE
             IN 1 + Card[T \ {elem}]
    IN Card[S]

\* Initial state: arbitrary values for all processes
Init == x \in [0..(N-1) -> 0..(K-1)]

\* Process 0 action: increment value mod K when it matches the last process
Move0 == 
    /\ x[0] = x[N-1]
    /\ x' = [x EXCEPT ![0] = (x[0] + 1) % K]

\* Process i (i > 0) action: copy predecessor's value when they differ
MoveI(i) == 
    /\ i > 0
    /\ x[i] # x[i-1]
    /\ x' = [x EXCEPT ![i] = x[i-1]]

\* A process can move if it holds a token
Move(i) == IF i = 0 THEN Move0 ELSE MoveI(i)

\* Next state relation: some process with a token makes a move
Next == \E i \in 0..(N-1) : Move(i)

\* Fairness: weak fairness for each process action
Fairness == \A i \in 0..(N-1) : WF_vars(Move(i))

\* Complete specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
\* Safety and Liveness Properties
--------------------------------------------------------------------------------

\* Safety: There is always at least one token holder
AtLeastOneToken == TokenHolders # {}

\* A legitimate state has exactly one token
SingleToken == Cardinality(TokenHolders) = 1

\* Liveness: Eventually we reach a state with exactly one token
EventuallySingleToken == <>SingleToken

\* Once we have a single token, we always have exactly one token
\* (This is the stability property of the legitimate state)
StableSingleToken == [](SingleToken => []SingleToken)

\* Combined convergence property: eventually stabilize to single token
Convergence == <>[]SingleToken

--------------------------------------------------------------------------------
\* Theorems
--------------------------------------------------------------------------------

THEOREM Safety == Spec => []AtLeastOneToken

THEOREM Liveness == Spec => EventuallySingleToken

THEOREM Stability == Spec => StableSingleToken

THEOREM ConvergenceTheorem == Spec => Convergence

================================================================================
---------------------------- MODULE dijkstra ----------------------------
EXTENDS Naturals, Integers

CONSTANTS N, K

ASSUME NKAssumption == K > N /\ N > 0

VARIABLES M, pc

vars == <<M, pc>>

ProcSet == (0..N-1)

\* A process holds a token if it can act
HasToken(i) == IF i = 0 
               THEN M[0] = M[N-1] 
               ELSE M[i] # M[i-1]

\* Initial state: arbitrary values for M, all processes start at "check" step
Init == /\ M \in [0..N-1 -> 0..K-1]
        /\ pc = [self \in ProcSet |-> "check"]

\* Process 0 (bottom): holds token when M[0] = M[N-1], increments mod K
P0_check == /\ pc[0] = "check"
            /\ M[0] = M[N-1]
            /\ pc' = [pc EXCEPT ![0] = "act"]
            /\ M' = M

P0_act == /\ pc[0] = "act"
          /\ M' = [M EXCEPT ![0] = (M[0] + 1) % K]
          /\ pc' = [pc EXCEPT ![0] = "check"]

P0_skip == /\ pc[0] = "check"
           /\ M[0] # M[N-1]
           /\ pc' = [pc EXCEPT ![0] = "check"]
           /\ M' = M

\* Process i > 0: holds token when M[i] # M[i-1], copies neighbor's value
Pi_check(i) == /\ i > 0
               /\ pc[i] = "check"
               /\ M[i] # M[i-1]
               /\ pc' = [pc EXCEPT ![i] = "act"]
               /\ M' = M

Pi_act(i) == /\ i > 0
             /\ pc[i] = "act"
             /\ M' = [M EXCEPT ![i] = M[i-1]]
             /\ pc' = [pc EXCEPT ![i] = "check"]

Pi_skip(i) == /\ i > 0
              /\ pc[i] = "check"
              /\ M[i] = M[i-1]
              /\ pc' = [pc EXCEPT ![i] = "check"]
              /\ M' = M

\* Combined actions for each process
P0 == P0_check \/ P0_act \/ P0_skip

Pi(i) == Pi_check(i) \/ Pi_act(i) \/ Pi_skip(i)

\* Next state relation
Next == P0 \/ \E i \in 1..N-1 : Pi(i)

\* Fairness conditions for all processes
Fairness == /\ WF_vars(P0_check \/ P0_act)
            /\ \A i \in 1..N-1 : WF_vars(Pi_check(i) \/ Pi_act(i))

\* Complete specification with weak fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Count of tokens in the system
TokenCount == Cardinality({i \in 0..N-1 : HasToken(i)})

\* Helper to define cardinality using recursive sum
RECURSIVE CountTokens(_)
CountTokens(S) == IF S = {} THEN 0
                  ELSE LET x == CHOOSE y \in S : TRUE
                       IN (IF HasToken(x) THEN 1 ELSE 0) + CountTokens(S \ {x})

NumTokens == CountTokens(0..N-1)

\* Invariant: at least one process always holds a token
SomeoneHoldsToken == \E i \in 0..N-1 : HasToken(i)

\* Single token condition
SingleToken == NumTokens = 1

\* Token passes condition (for state space analysis)
TokenPasses == \E i \in 0..N-1 : HasToken(i)

\* Liveness: eventually exactly one token forever (self-stabilization)
EventuallyJustOneHoldsToken == <>[]SingleToken

==========================================================================
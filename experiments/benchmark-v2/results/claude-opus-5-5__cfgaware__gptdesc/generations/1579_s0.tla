---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NAssumption == N \in Nat /\ N > 0
ASSUME KAssumption == K \in Nat /\ K > N

Procs == 0..(N-1)

(***************************************************************************
--algorithm TokenRing {
    variable x \in [Procs -> 0..(K-1)];

    fair process (P \in Procs) {
      a: while (TRUE) {
           if (self = 0) {
               await x[0] = x[N-1];
               x[0] := (x[0] + 1) % K
           } else {
               await x[self] # x[self-1];
               x[self] := x[self-1]
           }
         }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE x

vars == << x >>

ProcSet == Procs

Init == x \in [Procs -> 0..(K-1)]

P(self) ==
    IF self = 0
       THEN /\ x[0] = x[N-1]
            /\ x' = [x EXCEPT ![0] = (x[0] + 1) % K]
       ELSE /\ x[self] # x[self-1]
            /\ x' = [x EXCEPT ![self] = x[self-1]]

Next == \E self \in Procs : P(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(P(self))
\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == x \in [Procs -> 0..(K-1)]

HoldsToken(i) ==
    IF i = 0 THEN x[0] = x[N-1]
             ELSE x[i] # x[i-1]

TokenHolders == { i \in Procs : HoldsToken(i) }

SomeoneHoldsToken == \E i \in Procs : HoldsToken(i)

EventuallyJustOneHoldsToken ==
    <>[](\E i \in Procs : \A j \in Procs : HoldsToken(j) <=> (j = i))

\* Number of token holders is always between 1 and N.
PossibleCounts == Cardinality(TokenHolders) \in 1..N

\* Eventually the system stabilizes to a single token.
SingleToken == <>[](Cardinality(TokenHolders) = 1)

\* The token keeps circulating: process 0 holds the token infinitely often.
TokenPasses == []<>(HoldsToken(0))

\* Combined liveness / possibility property.
_POSSIBLE == SingleToken /\ TokenPasses

-----------------------------------------------------------------------------

THEOREM Spec => []TypeOK
THEOREM Spec => []SomeoneHoldsToken
THEOREM Spec => []PossibleCounts
THEOREM Spec => EventuallyJustOneHoldsToken
THEOREM Spec => SingleToken
THEOREM Spec => TokenPasses

=============================================================================
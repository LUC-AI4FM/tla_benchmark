---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NAssump == N \in Nat /\ N > 0
ASSUME KAssump == K \in Nat /\ K > N

Procs == 0..(N-1)

(***************************************************************************
--algorithm DijkstraTokenRing {
    variable x \in [Procs -> 0..(K-1)];
    fair process (p \in Procs) {
      l: while (TRUE) {
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

p(self) == IF self = 0
              THEN /\ x[0] = x[N-1]
                   /\ x' = [x EXCEPT ![0] = (x[0] + 1) % K]
              ELSE /\ x[self] # x[self-1]
                   /\ x' = [x EXCEPT ![self] = x[self-1]]

Next == \E self \in Procs : p(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))
\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == x \in [Procs -> 0..(K-1)]

HasToken(i) == IF i = 0 THEN x[0] = x[N-1] ELSE x[i] # x[i-1]

TokenHolders == {i \in Procs : HasToken(i)}

\* Safety: some process always holds a token
AlwaysAToken == \E i \in Procs : HasToken(i)

\* Legitimate state: exactly one token holder
UniqueToken == Cardinality(TokenHolders) = 1

\* Liveness: eventually the ring converges to (and stays in) a single-token state
Stabilization == <>[]UniqueToken

EventuallyUnique == <>UniqueToken

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM TokenAlwaysExists == Spec => []AlwaysAToken

THEOREM Converges == Spec => Stabilization

=============================================================================
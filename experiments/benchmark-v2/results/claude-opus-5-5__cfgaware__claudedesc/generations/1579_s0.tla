------------------------------ MODULE TokenRing ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, K

ASSUME NAssumption == N \in Nat \ {0}
ASSUME KAssumption == K \in Nat \ {0} /\ K > N

Procs  == 0 .. N-1
Values == 0 .. K-1

(* --algorithm TokenRing {
     variable M \in [Procs -> Values];
     fair process (i \in Procs) {
       w: while (TRUE) {
            if (self = 0) {
              await M[0] = M[N-1];
              M[0] := (M[0] + 1) % K
            } else {
              await M[self] # M[self-1];
              M[self] := M[self-1]
            }
          }
     }
   } *)
\* BEGIN TRANSLATION
VARIABLES M, pc

vars == << M, pc >>

ProcSet == Procs

Init == /\ M \in [Procs -> Values]
        /\ pc = [self \in ProcSet |-> "w"]

w(self) == /\ pc[self] = "w"
           /\ IF self = 0
                 THEN /\ M[0] = M[N-1]
                      /\ M' = [M EXCEPT ![0] = (M[0] + 1) % K]
                 ELSE /\ M[self] # M[self-1]
                      /\ M' = [M EXCEPT ![self] = M[self-1]]
           /\ pc' = [pc EXCEPT ![self] = "w"]

i(self) == w(self)

Next == \E self \in Procs : i(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(i(self))
\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ M \in [Procs -> Values]
          /\ pc \in [Procs -> {"w"}]

HasToken(m, p) == IF p = 0 THEN m[0] = m[N-1] ELSE m[p] # m[p-1]

TokensOf(m) == {p \in Procs : HasToken(m, p)}

UniqueToken(p) == TokensOf(M) = {p}

SomeoneHoldsToken == \E p \in Procs : HasToken(M, p)

EventuallyJustOneHoldsToken == <>[](\E p \in Procs : UniqueToken(p))

-----------------------------------------------------------------------------
\* Possibility checks over the (full) state space.

\* A state in which exactly one process holds a token.
SingleToken == Cardinality(TokensOf(M)) = 1

\* A state in which the unique token is held by a non-bottom process,
\* i.e., the token has been passed along the ring away from process 0.
TokenPasses == \E p \in Procs \ {0} : UniqueToken(p)

SingleTokenAt(m) == Cardinality(TokensOf(m)) = 1
TokenPassesAt(m) == \E p \in Procs \ {0} : TokensOf(m) = {p}

_POSSIBLE == TRUE

AllStates == [Procs -> Values]

PossibleCounts ==
    LET singles == Cardinality({m \in AllStates : SingleTokenAt(m)})
        passes  == Cardinality({m \in AllStates : TokenPassesAt(m)})
    IN  /\ TLCGet("stats").distinct > 0
        /\ singles > 0
        /\ passes > 0
        /\ passes <= singles
=============================================================================
---------------------------- MODULE TokenRing ----------------------------
(***************************************************************************)
(* Dijkstra's self-stabilizing token ring (K-state machine solution).     *)
(* N processes 0..N-1 arranged in a ring, each holding a value in 0..K-1.  *)
(* Process 0 holds a token when M[0] = M[N-1] and then increments its      *)
(* value modulo K.  Process i > 0 holds a token when M[i] # M[i-1] and     *)
(* then copies M[i-1].                                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NAssumption == N \in Nat \ {0}
ASSUME KAssumption == K \in Nat /\ K > N

Procs  == 0 .. (N - 1)
Values == 0 .. (K - 1)

(***************************************************************************
--algorithm TokenRing {
    variables M \in [Procs -> Values];

    define {
        Token(i) == IF i = 0 THEN M[0] = M[N-1] ELSE M[i] # M[i-1]
    }

    fair process (p \in Procs) {
      l: while (TRUE) {
           await Token(self);
           M[self] := IF self = 0 THEN (M[0] + 1) % K ELSE M[self - 1]
         }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES M, pc

(* define statement *)
Token(i) == IF i = 0 THEN M[0] = M[N-1] ELSE M[i] # M[i-1]

vars == << M, pc >>

ProcSet == Procs

Init == /\ M \in [Procs -> Values]
        /\ pc = [self \in ProcSet |-> "l"]

l(self) == /\ pc[self] = "l"
           /\ Token(self)
           /\ M' = [M EXCEPT ![self] = IF self = 0
                                          THEN (M[0] + 1) % K
                                          ELSE M[self - 1]]
           /\ pc' = [pc EXCEPT ![self] = "l"]

p(self) == l(self)

Next == \E self \in Procs : p(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK == /\ M \in [Procs -> Values]
          /\ pc \in [Procs -> {"l"}]

TokenHolders == {i \in Procs : Token(i)}

\* Invariant: at least one process always holds a token.
SomeoneHoldsToken == \E i \in Procs : Token(i)

\* Exactly one process holds a token.
SingleToken == Cardinality(TokenHolders) = 1

\* Once there is a single token, it remains single (it is merely passed on).
TokenPasses == [][SingleToken => SingleToken']_vars

\* Self-stabilization: eventually exactly one process holds the token forever.
EventuallyJustOneHoldsToken == <>[]SingleToken

THEOREM Spec => []TypeOK
THEOREM Spec => []SomeoneHoldsToken
THEOREM Spec => EventuallyJustOneHoldsToken
=============================================================================
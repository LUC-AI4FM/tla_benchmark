------------------------------ MODULE TokenRing ------------------------------
(***************************************************************************)
(* Dijkstra's first self-stabilizing token ring algorithm (K-state).       *)
(* N processes 0..N-1 arranged in a ring, each with a local value in       *)
(* 0..K-1, where K > N and N > 0.                                          *)
(*                                                                         *)
(*  - Process 0 holds a token iff its value equals that of process N-1.    *)
(*    When it holds a token, it increments its value modulo K.             *)
(*  - Process i > 0 holds a token iff its value differs from that of its   *)
(*    predecessor i-1. When it holds a token, it copies the value of its   *)
(*    predecessor.                                                         *)
(*                                                                         *)
(* Starting from an arbitrary state, the system converges to a legitimate  *)
(* state in which exactly one process holds a token.                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NKAssump == /\ N \in Nat \ {0}
                   /\ K \in Nat
                   /\ K > N

Procs  == 0 .. (N-1)
Values == 0 .. (K-1)

(***************************************************************************
--fair algorithm TokenRing {
    variable c \in [Procs -> Values];

    define {
        TokenAt(i) == IF i = 0 THEN c[0] = c[N-1]
                               ELSE c[i] # c[i-1]
    }

    fair process (p \in Procs) {
      n: while (TRUE) {
           await TokenAt(self);
           if (self = 0) c[self] := (c[self] + 1) % K
           else c[self] := c[self-1]
         }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE c

(* define statement *)
TokenAt(i) == IF i = 0 THEN c[0] = c[N-1]
                       ELSE c[i] # c[i-1]

vars == << c >>

ProcSet == Procs

Init == (* Global variables *)
        /\ c \in [Procs -> Values]

n(self) == /\ TokenAt(self)
           /\ IF self = 0
                 THEN c' = [c EXCEPT ![self] = (c[self] + 1) % K]
                 ELSE c' = [c EXCEPT ![self] = c[self-1]]

p(self) == n(self)

Next == (\E self \in Procs : p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK == c \in [Procs -> Values]

TokenHolders == { i \in Procs : TokenAt(i) }

(* Safety: some process always holds a token (the system never deadlocks) *)
SomeToken == TokenHolders # {}

(* Legitimate state: exactly one process holds the token *)
UniqueToken == Cardinality(TokenHolders) = 1

(* Liveness: eventually exactly one token holder remains forever *)
Stabilization == <>[]UniqueToken

(* Once legitimate, the system stays legitimate *)
Closure == [](UniqueToken => []UniqueToken)

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM AlwaysSomeToken == Spec => []SomeToken

THEOREM Convergence == Spec => Stabilization

THEOREM ClosureThm == Spec => Closure
=============================================================================
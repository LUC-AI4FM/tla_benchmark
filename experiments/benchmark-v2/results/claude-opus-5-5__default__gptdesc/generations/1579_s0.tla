------------------------------ MODULE SSToken ------------------------------
(***************************************************************************)
(* Dijkstra's first self-stabilizing token ring algorithm.                 *)
(*                                                                         *)
(* N processes, numbered 0..N-1, are arranged in a ring. Each process i    *)
(* holds a local value c[i] in 0..(K-1), with K > N and N > 0.             *)
(*                                                                         *)
(*  - Process 0 holds the token when c[0] = c[N-1]. It then increments its *)
(*    value modulo K.                                                      *)
(*  - Process i > 0 holds the token when c[i] # c[i-1]. It then copies its *)
(*    predecessor's value.                                                 *)
(*                                                                         *)
(* From any initial state, the ring converges to a state where exactly one *)
(* process holds the token.                                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NAssump == N \in Nat \ {0}
ASSUME KAssump == K \in Nat /\ K > N

Procs == 0..(N-1)

(***************************************************************************
--algorithm TokenRing {
    variable c \in [Procs -> 0..(K-1)];

    fair process (P \in Procs) {
      lp: while (TRUE) {
            if (self = 0) {
                await c[0] = c[N-1];
                c[0] := (c[N-1] + 1) % K
            } else {
                await c[self] # c[self-1];
                c[self] := c[self-1]
            }
          }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLE c

vars == << c >>

ProcSet == Procs

Init == (* Global variables *)
        /\ c \in [Procs -> 0..(K-1)]

P(self) == IF self = 0
              THEN /\ c[0] = c[N-1]
                   /\ c' = [c EXCEPT ![0] = (c[N-1] + 1) % K]
              ELSE /\ c[self] # c[self-1]
                   /\ c' = [c EXCEPT ![self] = c[self-1]]

Next == \E self \in Procs : P(self)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(P(self))
\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness                                                        *)
(***************************************************************************)
TypeOK == c \in [Procs -> 0..(K-1)]

(***************************************************************************)
(* Token definitions                                                       *)
(***************************************************************************)
HasToken(i) == IF i = 0 THEN c[0] = c[N-1]
                        ELSE c[i] # c[i-1]

TokenHolders == {i \in Procs : HasToken(i)}

(***************************************************************************)
(* Safety: some process always holds a token (no deadlock).                *)
(***************************************************************************)
SomeoneHoldsToken == TokenHolders # {}

(***************************************************************************)
(* Legitimate state: exactly one token holder.                             *)
(***************************************************************************)
Legitimate == Cardinality(TokenHolders) = 1

(***************************************************************************)
(* Liveness: eventually the system stabilizes to exactly one token holder  *)
(* and remains so forever.                                                 *)
(***************************************************************************)
Stabilization == <>[]Legitimate

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM Safety == Spec => []SomeoneHoldsToken

THEOREM Convergence == Spec => Stabilization

THEOREM Closure == Spec => [](Legitimate => []Legitimate)
=============================================================================
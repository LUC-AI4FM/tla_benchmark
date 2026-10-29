---------------------------- MODULE SSToken ----------------------------
(***************************************************************************)
(* Dijkstra's first self-stabilizing token ring algorithm.                 *)
(*                                                                         *)
(* There are N processes, numbered 0 .. N-1, arranged in a ring. Each      *)
(* process i holds a local value c[i] in 0 .. K-1. We assume K > N > 0.    *)
(*                                                                         *)
(*  - Process 0 holds a token iff c[0] = c[N-1]. When it does, it          *)
(*    increments its value modulo K.                                       *)
(*  - Process i > 0 holds a token iff c[i] # c[i-1]. When it does, it      *)
(*    copies the value of its predecessor.                                 *)
(*                                                                         *)
(* From any initial state, the system converges to a state with exactly   *)
(* one token, and it stays in such states from then on.                    *)
(*                                                                         *)
(* --algorithm SSToken {                                                   *)
(*   variable c \in [0..N-1 -> 0..K-1];                                    *)
(*   fair process (P \in 0..N-1) {                                         *)
(*     a: while (TRUE) {                                                   *)
(*          if (self = 0) {                                                *)
(*            await c[0] = c[N-1];                                         *)
(*            c[0] := (c[0] + 1) % K                                       *)
(*          } else {                                                       *)
(*            await c[self] # c[self-1];                                   *)
(*            c[self] := c[self-1]                                         *)
(*          }                                                              *)
(*        }                                                                *)
(*   }                                                                     *)
(* }                                                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NKAssump == /\ N \in Nat \ {0}
                   /\ K \in Nat
                   /\ K > N

\* BEGIN TRANSLATION
VARIABLE c

vars == << c >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ c \in [0..N-1 -> 0..K-1]

P(self) == IF self = 0
              THEN /\ c[0] = c[N-1]
                   /\ c' = [c EXCEPT ![0] = (c[0] + 1) % K]
              ELSE /\ c[self] # c[self-1]
                   /\ c' = [c EXCEPT ![self] = c[self-1]]

Next == (\E self \in 0..N-1 : P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 0..N-1 : WF_vars(P(self))
\* END TRANSLATION
-------------------------------------------------------------------------

(* Type correctness *)
TypeOK == c \in [0..N-1 -> 0..K-1]

(* Process i holds a token *)
Token(i) == IF i = 0 THEN c[0] = c[N-1] ELSE c[i] # c[i-1]

(* The set of processes holding a token *)
TokenHolders == {i \in 0..N-1 : Token(i)}

(* Safety: some process always holds a token (no deadlock) *)
TokenAlwaysPresent == \E i \in 0..N-1 : Token(i)

(* Legitimate state: exactly one token holder *)
Legitimate == Cardinality(TokenHolders) = 1

(* Liveness: eventually exactly one token holder remains forever *)
Stabilization == <>[]Legitimate

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM AlwaysToken == Spec => []TokenAlwaysPresent

THEOREM Convergence == Spec => Stabilization

=========================================================================
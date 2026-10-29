------------------------------- MODULE DijkstraSelfStabilizingRing -------------------------------
(***************************************************************************)
(* Dijkstra's first self-stabilizing token ring algorithm (K-state).       *)
(* A ring of N processes, numbered 0..N-1, each holding a local value in   *)
(* 0..(K-1), with K > N and N > 0.                                         *)
(*                                                                         *)
(*  - Process 0 holds a token when its value equals that of process N-1.   *)
(*    It then increments its value modulo K.                               *)
(*  - Process i > 0 holds a token when its value differs from that of its  *)
(*    predecessor i-1. It then copies its predecessor's value.             *)
(*                                                                         *)
(* From any initial state, the ring converges to a legitimate state in     *)
(* which exactly one process holds the token.                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NKAssump == /\ N \in Nat \ {0}
                   /\ K \in Nat
                   /\ K > N

Procs == 0 .. (N - 1)
Vals  == 0 .. (K - 1)

(***************************************************************************
--algorithm DijkstraRing {
    variable x \in [Procs -> Vals];

    fair process (P \in Procs) {
      loop: while (TRUE) {
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

Init == x \in [Procs -> Vals]

P(self) == IF self = 0
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
(***************************************************************************)
(* Token definitions and properties.                                       *)
(***************************************************************************)
TypeOK == x \in [Procs -> Vals]

HasToken(i) == IF i = 0 THEN x[0] = x[N-1]
                        ELSE x[i] # x[i-1]

TokenHolders == {i \in Procs : HasToken(i)}

\* Safety: some process always holds a token (no deadlock).
AlwaysAToken == \E i \in Procs : HasToken(i)

\* Legitimate state: exactly one process holds the token.
UniqueToken == \E i \in Procs : TokenHolders = {i}

\* Liveness: eventually the system stabilizes with exactly one token holder.
Stabilization == <>[]UniqueToken

\* Alternative formulation: eventually exactly one token.
EventuallyUnique == <>UniqueToken

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM TokenAlwaysExists == Spec => []AlwaysAToken

THEOREM Convergence == Spec => Stabilization

THEOREM ReachesLegitimate == Spec => EventuallyUnique
=============================================================================
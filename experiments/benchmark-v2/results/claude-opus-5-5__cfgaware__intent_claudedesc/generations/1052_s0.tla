------------------------------ MODULE TokenRing ------------------------------
(***************************************************************************)
(* Dijkstra-style token ring for distributed mutual exclusion.             *)
(* N processes 0..N-1 are arranged in a unidirectional ring.  Each process *)
(* holds a counter in 0..M-1.  A process detects that it holds the token   *)
(* by comparing its counter with that of its predecessor:                  *)
(*   - process 0 holds the token iff x[0] = x[N-1]                         *)
(*   - process i > 0 holds the token iff x[i] # x[i-1]                     *)
(* Passing the token:                                                      *)
(*   - process 0 increments its counter modulo M                           *)
(*   - process i > 0 copies its predecessor's counter                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssump == N \in Nat /\ N >= 1
ASSUME MAssump == M \in Nat /\ M >= 1

VARIABLE x

vars == << x >>

Procs  == 0 .. (N - 1)
Values == 0 .. (M - 1)

TypeOK == x \in [Procs -> Values]

HasToken(i) ==
    IF i = 0 THEN x[0] = x[N - 1]
             ELSE x[i] # x[i - 1]

TokenHolders == { i \in Procs : HasToken(i) }

(* Legitimate initial configuration: all counters equal, so process 0 holds the token. *)
Init == \E v \in Values : x = [i \in Procs |-> v]

PassToken(i) ==
    /\ HasToken(i)
    /\ x' = [x EXCEPT ![i] = IF i = 0 THEN (x[0] + 1) % M
                                      ELSE x[i - 1]]

Next == \E i \in Procs : PassToken(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety *)
MutualExclusion == Cardinality(TokenHolders) <= 1

ExactlyOneToken == Cardinality(TokenHolders) = 1

(* Progress: some process can always move the token *)
NoDeadlock == \E i \in Procs : HasToken(i)

(* Liveness *)
TokenCirculation == \A i \in Procs : []<>HasToken(i)

Progress == []<>(ENABLED Next)

=============================================================================
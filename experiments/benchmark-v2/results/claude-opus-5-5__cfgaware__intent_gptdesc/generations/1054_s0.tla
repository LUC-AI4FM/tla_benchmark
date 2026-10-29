---------------------------- MODULE TokenRing ----------------------------
(***************************************************************************)
(* Dijkstra's K-state self-stabilizing token ring.                         *)
(*                                                                         *)
(* N processes 0..N-1 form a unidirectional ring. Process i's predecessor  *)
(* is i-1, and process 0's predecessor is N-1.                             *)
(* Each process holds a counter in 0..M-1.                                 *)
(*                                                                         *)
(*  - Process 0 (the source) is privileged when c[0] = c[N-1]. It then     *)
(*    injects a new token by setting c[0] to (c[0] + 1) % M.               *)
(*  - Process i > 0 is privileged when c[i] # c[i-1]. It then copies its   *)
(*    predecessor's value.                                                 *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS N, M

ASSUME NAssumption == N \in Nat /\ N >= 2
ASSUME MAssumption == M \in Nat /\ M >= N   \* K >= N guarantees stabilization

VARIABLE c

vars == << c >>

Procs  == 0 .. (N - 1)
Values == 0 .. (M - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

-----------------------------------------------------------------------------
TypeOK == c \in [Procs -> Values]

\* Any configuration of counters is a possible initial state.
Init == c \in [Procs -> Values]

\* Privilege (token possession) predicate.
Privileged(i) ==
    IF i = 0 THEN c[0] = c[N - 1]
             ELSE c[i] # c[i - 1]

\* The source process creates or injects a token.
Inject ==
    /\ c[0] = c[N - 1]
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

\* A non-source process copies its predecessor's value, passing the token.
Pass(i) ==
    /\ i # 0
    /\ c[i] # c[i - 1]
    /\ c' = [c EXCEPT ![i] = c[i - 1]]

Next == Inject \/ \E i \in Procs \ {0} : Pass(i)

Fairness ==
    /\ WF_vars(Inject)
    /\ \A i \in Procs \ {0} : WF_vars(Pass(i))
    /\ WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Legitimate configuration: a single boundary. Processes 0..j-1 hold v    *)
(* and processes j..N-1 hold (v-1) mod M, for some j in 0..N.              *)
(* When j = 0 or j = N, all counters are equal and process 0 holds the     *)
(* token. Otherwise process j holds the unique token.                      *)
(***************************************************************************)
Legit ==
    \E v \in Values, j \in 0 .. N :
        \A i \in Procs :
            c[i] = IF i < j THEN v ELSE (v + M - 1) % M

NumPrivileged ==
    LET S == {i \in Procs : Privileged(i)}
    IN  IF S = {} THEN 0 ELSE
        CHOOSE n \in 1 .. N : \E f \in [1 .. n -> S] :
            \A s \in S : \E k \in 1 .. n : f[k] = s
                /\ \A a, b \in 1 .. n : a # b => f[a] # f[b]

\* Safety: counters stay within the finite domain.
Safety == []TypeOK

\* Self-stabilization: the system eventually becomes legitimate and stays so.
Stab == <>[]Legit

\* Closure: once legitimate, the system remains legitimate.
Closure == [](Legit => []Legit)

\* Alias used for readable error traces.
Alias ==
    [ c          |-> c,
      legit      |-> Legit,
      privileged |-> {i \in Procs : Privileged(i)} ]

=============================================================================
------------------------------ MODULE StabilizingTokenRing ------------------------------
(***************************************************************************)
(* Dijkstra's K-state self-stabilizing token ring.                         *)
(* N processes 0..N-1 are arranged in a unidirectional ring, and each      *)
(* process i reads the counter of its predecessor (i-1) mod N.             *)
(* Process 0 is the distinguished source. When its counter equals that of  *)
(* its predecessor N-1, it injects a new token value by incrementing its   *)
(* counter modulo M.                                                       *)
(* Every other process i copies its predecessor's counter when the two     *)
(* values differ.                                                          *)
(* A process is "privileged" (holds a token) exactly when its action is    *)
(* enabled.                                                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,   \* number of processes in the ring
          M    \* size of the counter domain 0..M-1

ASSUME NMAssumption ==
    /\ N \in Nat /\ N >= 2
    /\ M \in Nat /\ M >= N      \* domain at least as large as the ring

VARIABLES c    \* c[i] is the counter of process i

vars == << c >>

Procs  == 0 .. (N - 1)
Domain == 0 .. (M - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

-----------------------------------------------------------------------------
(* Privilege (token) predicates *)

Privileged(i) ==
    IF i = 0 THEN c[0] = c[N - 1]
             ELSE c[i] # c[i - 1]

PrivilegedSet == { i \in Procs : Privileged(i) }

-----------------------------------------------------------------------------
(* Initial state: arbitrary counters in the domain *)

Init == c \in [Procs -> Domain]

(* Source process injects a token by incrementing modulo M *)
Inject ==
    /\ c[0] = c[N - 1]
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

(* Non-source process i copies its predecessor's value *)
Pass(i) ==
    /\ i # 0
    /\ c[i] # c[i - 1]
    /\ c' = [c EXCEPT ![i] = c[i - 1]]

Step(i) == IF i = 0 THEN Inject ELSE Pass(i)

Next == \E i \in Procs : Step(i)

(* Weak fairness on each local action: a continuously enabled
   injection or pass cannot be postponed forever. *)
Fairness == \A i \in Procs : WF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

TypeOK == c \in [Procs -> Domain]

(* No illegal counter values ever occur *)
DomainSafety == \A i \in Procs : c[i] \in Domain

(* At least one process is always privileged, so there is no deadlock *)
NoDeadlock == PrivilegedSet # {}

-----------------------------------------------------------------------------
(* Canonical unique-token configuration.                                   *)
(* For some value v and boundary k in 1..N:                                *)
(*   processes 0..k-1 hold v, and processes k..N-1 hold (v-1) mod M.       *)
(* If k = N, all counters equal v and the single token is at process 0     *)
(* (the boundary lies between N-1 and 0). Otherwise the token is at k.    *)

Legit ==
    \E v \in Domain, k \in 1 .. N :
        \A i \in Procs :
            c[i] = IF i < k THEN v ELSE (v + M - 1) % M

(* Exactly one logical token *)
UniqueToken == Cardinality(PrivilegedSet) = 1

-----------------------------------------------------------------------------
(* Correctness properties *)

(* A canonical configuration has exactly one token *)
LegitImpliesUnique == Legit => UniqueToken

(* Closure: once legitimate, the system stays legitimate *)
Closure == [](Legit => []Legit)

(* Convergence and self-stabilization: from any initial configuration the
   system eventually reaches, and thereafter keeps, the canonical
   configuration *)
Convergence       == <>Legit
SelfStabilization == <>[]Legit

(* The token circulates: every process is privileged infinitely often *)
TokenCirculates == \A i \in Procs : []<>Privileged(i)

(* Repeated injections occur forever *)
InfiniteInjection == []<>(ENABLED Inject)

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []DomainSafety
THEOREM Spec => []NoDeadlock
THEOREM Spec => []LegitImpliesUnique
THEOREM Spec => Closure
THEOREM Spec => SelfStabilization
THEOREM Spec => TokenCirculates
=============================================================================
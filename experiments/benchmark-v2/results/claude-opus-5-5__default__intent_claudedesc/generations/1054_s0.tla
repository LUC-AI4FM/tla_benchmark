---------------------------- MODULE EWD426 ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NAssumption == N \in Nat /\ N >= 1
ASSUME MAssumption == M \in Nat /\ M >= 1
ASSUME RingAssumption == N <= M + 1

VARIABLE c

vars == << c >>

Nodes  == 0 .. (N - 1)
Values == 0 .. (M - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

(* A node is privileged, meaning it holds a token, according to Dijkstra's rules. *)
Privileged(i) ==
    IF i = 0 THEN c[0] = c[Pred(0)]
             ELSE c[i] # c[Pred(i)]

PrivilegedNodes == { i \in Nodes : Privileged(i) }

TypeOK == c \in [Nodes -> Values]

(* The system may start in any arbitrary configuration. *)
Init == c \in [Nodes -> Values]

(* Node 0 advances the token by incrementing its counter modulo M. *)
MoveZero ==
    /\ Privileged(0)
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % M]

(* Node i > 0 passes the token by copying its predecessor's value. *)
MoveOther(i) ==
    /\ i # 0
    /\ Privileged(i)
    /\ c' = [c EXCEPT ![i] = c[Pred(i)]]

Move(i) == IF i = 0 THEN MoveZero ELSE MoveOther(i)

Next == \E i \in Nodes : Move(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Nodes : WF_vars(Move(i))

---------------------------------------------------------------------------
(* Safety properties *)

(* There is always at least one token, so the system never deadlocks. *)
AtLeastOneToken == PrivilegedNodes # {}

(* There is exactly one token in the ring. *)
UniqueToken == Cardinality(PrivilegedNodes) = 1

(* Structural characterization of a legitimate configuration.
   There is a unique transition point j. Every node before j agrees with
   node 0's value. Every node from j onward holds the predecessor value,
   which is node N-1's value. The token is at j when c[0] # c[N-1].
   Otherwise all counters are equal and the token is at node 0. *)
Legitimate ==
    \/ \A i \in Nodes : c[i] = c[0]
    \/ \E j \in 1 .. (N - 1) :
          /\ c[0] # c[N - 1]
          /\ \A i \in Nodes :
                c[i] = IF i < j THEN c[0] ELSE c[N - 1]

(* The structural form is equivalent to having exactly one token. *)
LegitimateIffUnique == Legitimate <=> UniqueToken

(* Closure: once legitimate, the system stays legitimate. *)
Closure == [](UniqueToken => []UniqueToken)

---------------------------------------------------------------------------
(* Liveness property *)

(* Stabilization: from any initial state, the system eventually reaches
   a configuration with exactly one token and remains there forever. *)
Stabilization == <>[]UniqueToken

StabilizationLegit == <>[]Legitimate

---------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []AtLeastOneToken
THEOREM Spec => []LegitimateIffUnique
THEOREM Spec => Closure
THEOREM Spec => Stabilization
THEOREM Spec => StabilizationLegit
===========================================================================
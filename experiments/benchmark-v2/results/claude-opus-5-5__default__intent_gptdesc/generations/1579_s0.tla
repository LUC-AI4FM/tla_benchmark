------------------------------ MODULE KStateTokenRing ------------------------------
(***************************************************************************)
(* Dijkstra's K-state self-stabilizing token circulation on a              *)
(* unidirectional ring of N processes 0..N-1, with K > N counter values.   *)
(*                                                                         *)
(* Process 0 is the designated initiator (the "bottom" process).           *)
(*   Process 0 holds the token  iff  c[0] = c[N-1].                        *)
(*   Process i # 0 holds token  iff  c[i] # c[i-1].                        *)
(* Moves:                                                                  *)
(*   Process 0 increments its counter modulo K.                            *)
(*   Process i # 0 copies its predecessor's counter.                       *)
(*                                                                         *)
(* Starting from an arbitrary configuration, the system converges to, and  *)
(* then stays in, states in which exactly one process holds the token.     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME NAssumption == N \in Nat /\ N > 0
ASSUME KAssumption == K \in Nat /\ K > N

Procs  == 0 .. (N - 1)
Values == 0 .. (K - 1)

VARIABLES c

vars == << c >>

(* Predecessor on the unidirectional ring *)
Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

(* Token semantics *)
HasToken(i) ==
    IF i = 0 THEN c[0] = c[N - 1]
             ELSE c[i] # c[Pred(i)]

Holders == { i \in Procs : HasToken(i) }

-----------------------------------------------------------------------------
TypeOK == c \in [Procs -> Values]

(* Arbitrary initial configuration (self-stabilization) *)
Init == c \in [Procs -> Values]

(* Initiator: increments its counter when it holds the token *)
InitiatorStep ==
    /\ HasToken(0)
    /\ c' = [c EXCEPT ![0] = (c[0] + 1) % K]

(* Other processes: copy predecessor's counter when holding the token *)
OtherStep(i) ==
    /\ i # 0
    /\ HasToken(i)
    /\ c' = [c EXCEPT ![i] = c[Pred(i)]]

Step(i) == IF i = 0 THEN InitiatorStep ELSE OtherStep(i)

(* Asynchronous interleaving: one process moves at a time *)
Next == \E i \in Procs : Step(i)

Fairness == \A i \in Procs : WF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* At least one process always holds the token *)
TokenExistence == Holders # {}

(* Consequently the system never deadlocks *)
NoDeadlock == ENABLED Next

Legitimate == Cardinality(Holders) = 1

(* Once legitimate, the system stays legitimate *)
Closure == [](Legitimate => []Legitimate)

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Token-passing steps keep happening *)
Progress == []<><<Next>>_vars

(* The token circulates: every process holds it infinitely often *)
TokenCirculation == \A i \in Procs : []<>HasToken(i)

(* Every process makes token-passing moves infinitely often *)
EveryProcessMoves == \A i \in Procs : []<><<Step(i)>>_vars

(* Convergence: eventually exactly one token, and forever after *)
Convergence == <>[]Legitimate

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []TokenExistence
THEOREM Spec => Closure
THEOREM Spec => Progress
THEOREM Spec => TokenCirculation
THEOREM Spec => Convergence
=============================================================================
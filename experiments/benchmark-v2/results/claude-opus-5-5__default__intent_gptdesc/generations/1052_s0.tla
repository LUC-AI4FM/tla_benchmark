------------------------------ MODULE TokenRing ------------------------------
(***************************************************************************)
(* Parameterized token-passing ring of N processes.                        *)
(* Each process keeps a bounded counter in 0..M.  Exactly one token        *)
(* exists.  The holder first performs a local update (incrementing its     *)
(* counter modulo M+1) while momentarily keeping the token, and then       *)
(* forwards the token to its clockwise neighbor.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,  \* number of processes in the ring
          M   \* maximum counter value

ASSUME ParamAssumption == /\ N \in Nat /\ N > 1
                          /\ M \in Nat

VARIABLES holds,    \* holds[p] = TRUE iff process p holds the token
          counter,  \* counter[p] \in 0..M
          updated   \* TRUE iff current holder already did its local update

vars == <<holds, counter, updated>>

(***************************************************************************)
(* Ring structure and neighbor relation                                    *)
(***************************************************************************)
Proc == 0 .. (N - 1)

Succ(p) == (p + 1) % N          \* clockwise neighbor of p

Pred(p) == (p + N - 1) % N      \* counter-clockwise neighbor of p

Neighbor(p, q) == q = Succ(p)   \* q is the clockwise neighbor of p

TokenHolders == {p \in Proc : holds[p]}

NumTokens == Cardinality(TokenHolders)

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ holds   \in [Proc -> BOOLEAN]
    /\ counter \in [Proc -> 0 .. M]
    /\ updated \in BOOLEAN

(***************************************************************************)
(* Initial states: arbitrary counters, exactly one token holder            *)
(***************************************************************************)
Init ==
    /\ counter \in [Proc -> 0 .. M]
    /\ \E p0 \in Proc : holds = [q \in Proc |-> q = p0]
    /\ updated = FALSE

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
\* The holder keeps the token momentarily and updates its counter.
Update(p) ==
    /\ holds[p]
    /\ ~updated
    /\ counter' = [counter EXCEPT ![p] = (counter[p] + 1) % (M + 1)]
    /\ updated' = TRUE
    /\ UNCHANGED holds

\* After updating, the holder forwards the token to its clockwise neighbor.
Pass(p) ==
    /\ holds[p]
    /\ updated
    /\ holds' = [holds EXCEPT ![p] = FALSE, ![Succ(p)] = TRUE]
    /\ updated' = FALSE
    /\ UNCHANGED counter

Step(p) == Update(p) \/ Pass(p)

Next == \E p \in Proc : Step(p)

(***************************************************************************)
(* Fairness: every process that can update / pass eventually does so.      *)
(***************************************************************************)
Fairness == \A p \in Proc : /\ WF_vars(Update(p))
                            /\ WF_vars(Pass(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
\* Mutual exclusion: at most one process holds the token.
MutualExclusion ==
    \A p, q \in Proc : (holds[p] /\ holds[q]) => p = q

\* Conservation: exactly one token exists.
TokenConservation == NumTokens = 1

\* Counter bounds: every counter stays in 0..M.
CounterBounds == \A p \in Proc : counter[p] \in 0 .. M

\* Inductive invariant used for parameterized proofs.
Inv ==
    /\ TypeOK
    /\ \E h \in Proc : holds = [q \in Proc |-> q = h]

SafetyInv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ TokenConservation
    /\ CounterBounds

\* Transition-level safety: no step creates or destroys tokens.
NoTokenCreationOrLoss == [][NumTokens' = NumTokens]_vars

\* A token can only move from a process to its clockwise neighbor.
TokenMovesToNeighbor ==
    [][\A p, q \in Proc :
          (holds[p] /\ holds'[q] /\ p # q) => Neighbor(p, q)]_vars

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* Token circulation: every process eventually (and repeatedly) gets token.
TokenCirculation == \A p \in Proc : []<>holds[p]

\* From any state, every process will eventually hold the token.
EventuallyHolds == \A p \in Proc : TRUE ~> holds[p]

\* Progress on update: a holder eventually updates and passes the token.
UpdateProgress ==
    \A p \in Proc : (holds[p] /\ ~updated) ~> (holds[p] /\ updated)

PassProgress == \A p \in Proc : holds[p] ~> ~holds[p]

\* If p holds the token infinitely often, it updates and passes infinitely often.
InfinitelyOftenProgress ==
    \A p \in Proc :
        []<>holds[p] => ([]<><<Update(p)>>_vars /\ []<><<Pass(p)>>_vars)

(***************************************************************************)
(* Theorems (parameterized in N > 1 and M >= 0)                            *)
(***************************************************************************)
THEOREM InitEstablishesInv == ParamAssumption /\ Init => Inv

THEOREM InvInductive == ParamAssumption /\ Inv /\ [Next]_vars => Inv'

THEOREM InvImpliesSafety == ParamAssumption /\ Inv => SafetyInv

THEOREM SafetyTheorem ==
    Spec => /\ []TypeOK
            /\ []MutualExclusion
            /\ []TokenConservation
            /\ []CounterBounds
            /\ NoTokenCreationOrLoss
            /\ TokenMovesToNeighbor

THEOREM LivenessTheorem ==
    Spec => /\ TokenCirculation
            /\ EventuallyHolds
            /\ UpdateProgress
            /\ PassProgress
            /\ InfinitelyOftenProgress
=============================================================================
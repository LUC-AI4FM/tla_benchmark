------------------------------ MODULE TokenRing ------------------------------
(***************************************************************************)
(* Parameterized token-passing ring of N processes.  Each process keeps a *)
(* local counter in 0..M.  Exactly one token circulates clockwise.  The   *)
(* holder first performs a local update (counter incremented modulo M+1)  *)
(* while keeping the token, then forwards the token to its clockwise      *)
(* neighbor.                                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME NMAssumption == /\ N \in Nat /\ N > 1
                       /\ M \in Nat

Procs == 0 .. (N - 1)

\* Clockwise neighbor relation on the ring
Succ(p) == (p + 1) % N
Neighbor(p, q) == q = Succ(p)

VARIABLES counter,  \* counter[p] \in 0..M
          tok,      \* tok[p] = TRUE iff p holds the token
          updated   \* TRUE iff current holder already did its local update

vars == <<counter, tok, updated>>

Holders == {p \in Procs : tok[p]}

TypeOK ==
    /\ counter \in [Procs -> 0 .. M]
    /\ tok \in [Procs -> BOOLEAN]
    /\ updated \in BOOLEAN

Init ==
    /\ counter \in [Procs -> 0 .. M]
    /\ \E h \in Procs : tok = [p \in Procs |-> p = h]
    /\ updated = FALSE

(* Holder keeps the token momentarily and updates its counter *)
Update(p) ==
    /\ tok[p]
    /\ ~updated
    /\ counter' = [counter EXCEPT ![p] = (@ + 1) % (M + 1)]
    /\ updated' = TRUE
    /\ UNCHANGED tok

(* Holder forwards the token to its clockwise neighbor *)
Pass(p) ==
    /\ tok[p]
    /\ updated
    /\ tok' = [tok EXCEPT ![p] = FALSE, ![Succ(p)] = TRUE]
    /\ updated' = FALSE
    /\ UNCHANGED counter

Step(p) == Update(p) \/ Pass(p)

Next == \E p \in Procs : Step(p)

Fairness == \A p \in Procs : /\ WF_vars(Update(p))
                             /\ WF_vars(Pass(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

MutualExclusion ==
    \A p, q \in Procs : (tok[p] /\ tok[q]) => p = q

TokenConservation == Cardinality(Holders) = 1

CounterBounds == \A p \in Procs : counter[p] \in 0 .. M

Safety == TypeOK /\ MutualExclusion /\ TokenConservation /\ CounterBounds

(* Inductive invariant usable for parameterized reasoning *)
Inv == /\ TypeOK
       /\ \E h \in Procs : tok = [p \in Procs |-> p = h]

---------------------------------------------------------------------------
(* Liveness properties *)

TokenCirculation == \A p \in Procs : []<>(tok[p])

ProgressOnUpdate ==
    \A p \in Procs : (tok[p] /\ ~updated) ~> (tok[Succ(p)] /\ ~tok[p])

Liveness == TokenCirculation /\ ProgressOnUpdate

---------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================
------------------------------ MODULE HuangTermination ------------------------------
EXTENDS TLC

CONSTANTS ProcSet, Leader, MaxDenominator

VARIABLES weight, status, msgs

(* Derived constants *)
Nat == 0 .. MaxDenominator

(* Type invariant (optional) *)
TypeInvariant ==
  /\ weight ∈ [ProcSet -> Nat]
  /\ status ∈ [ProcSet -> {"idle","active"}]
  /\ msgs ∈ SUBSET [src: ProcSet, dst: ProcSet, w: Nat]

(* Initial state *)
Init ==
  /\ weight = [p \in ProcSet |-> IF p = Leader THEN MaxDenominator ELSE 0]
  /\ status = [p \in ProcSet |-> IF p = Leader THEN "active" ELSE "idle"]
  /\ msgs = {}

(* Actions *)

Activate(p) ==
  /\ p ∈ ProcSet
  /\ status[p] = "idle"
  /\ status' = [status EXCEPT ![p] = "active"]
  /\ UNCHANGED << weight, msgs >>

SendWeightAction(p) ==
  /\ p ∈ ProcSet
  /\ status[p] = "active"
  /\ q ∈ ProcSet \ {p}
  /\ w ∈ Nat
  /\ w <= weight[p]
  /\ msgs' = msgs ∪ { [src |-> p, dst |-> q, w |-> w] }
  /\ weight' = [weight EXCEPT ![p] = @ - w]
  /\ status' = status

ReceiveWeightAction(p) ==
  /\ p ∈ ProcSet
  /\ m \in msgs
  /\ m.dst = p
  /\ msgs' = msgs \ {m}
  /\ weight' = [weight EXCEPT ![p] = @ + m.w]
  /\ status' = status

IdleAction(p) ==
  /\ p ∈ ProcSet
  /\ status[p] = "active"
  /\ IF p = Leader THEN
       /\ status' = [status EXCEPT ![p] = "idle"]
       /\ msgs' = msgs
       /\ weight' = weight
     ELSE
       /\ msgs' = msgs ∪ { [src |-> p, dst |-> Leader, w |-> weight[p]] }
       /\ weight' = [weight EXCEPT ![p] = 0]
       /\ status' = [status EXCEPT ![p] = "idle"]

Next ==
  \E p \in ProcSet :
    Activate(p) \/ SendWeightAction(p) \/ ReceiveWeightAction(p) \/ IdleAction(p)

(* Derived predicates *)
TotalWeight == \Sum_{p \in ProcSet} weight[p] + \Sum_{m \in msgs} m.w

Terminated ==
  /\ status[Leader] = "idle"
  /\ weight[Leader] = MaxDenominator
  /\ msgs = {}
  /\ \A p \in ProcSet : status[p] = "idle"

Quiescent ==
  /\ msgs = {}
  /\ \A p \in ProcSet : status[p] = "idle"

vars == <<weight, status, msgs>>

Spec == Init /\ [][Next]_vars

SafetyProp == [] (Terminated => Terminated)

LivenessProp == [] (Quiescent => <> Terminated)

=============================================================================
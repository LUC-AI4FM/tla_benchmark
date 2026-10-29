---------------------------- MODULE CyclicCounter ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N > 0

VARIABLE x

vars == << x >>

-----------------------------------------------------------------------------
(* State space *)
TypeOK == x \in 0..(N-1)

(* Initial predicate *)
Init == x = 0

(* Next-state relation: increment modulo N *)
Increment == x' = (x + 1) % N

Next == Increment

(* All behaviors start from Init and every step is an Increment step
   (or a stuttering step, as required by TLA+). Weak fairness on Next
   rules out infinite stuttering, so the counter advances forever. *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety: the counter is always an integer in 0..N-1 *)
Safety == [](x \in 0..(N-1))

Inv == TypeOK

(* Liveness: from any reachable state, every residue is eventually visited *)
VisitsAll == \A v \in 0..(N-1) : []<>(x = v)

Liveness == VisitsAll

(* The counter keeps advancing forever *)
Progress == \A v \in 0..(N-1) : (x = v) ~> (x = (v + 1) % N)

THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================
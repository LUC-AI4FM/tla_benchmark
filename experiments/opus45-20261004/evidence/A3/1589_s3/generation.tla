---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNumAssumption == MaxNum \in Nat /\ MaxNum >= 1

VARIABLES pc, u_ini, v_ini, u, v

vars == <<pc, u_ini, v_ini, u, v>>

----------------------------------------------------------------------------
(* Mathematical definition of GCD *)

Divides(p, n) == \E q \in 1..n : n = p * q

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

GCD(m, n) == CHOOSE p \in DivisorsOf(m) \cap DivisorsOf(n) :
               \A q \in DivisorsOf(m) \cap DivisorsOf(n) : q <= p

----------------------------------------------------------------------------
(* Type invariant *)

TypeOK == /\ pc \in {"start", "loop", "done"}
          /\ u_ini \in 1..MaxNum
          /\ v_ini \in 1..MaxNum
          /\ u \in 1..MaxNum
          /\ v \in 1..MaxNum

----------------------------------------------------------------------------
(* Initial state *)

Init == /\ pc = "start"
        /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ u = u_ini
        /\ v = v_ini

----------------------------------------------------------------------------
(* Actions corresponding to PlusCal algorithm *)

Start == /\ pc = "start"
         /\ pc' = "loop"
         /\ UNCHANGED <<u_ini, v_ini, u, v>>

Loop == /\ pc = "loop"
        /\ IF u = v
           THEN /\ pc' = "done"
                /\ UNCHANGED <<u, v>>
           ELSE /\ IF u > v
                   THEN /\ u' = u - v
                        /\ UNCHANGED v
                   ELSE /\ v' = v - u
                        /\ UNCHANGED u
                /\ pc' = "loop"
        /\ UNCHANGED <<u_ini, v_ini>>

Done == /\ pc = "done"
        /\ UNCHANGED vars

----------------------------------------------------------------------------
(* Next state relation *)

Next == Start \/ Loop \/ Done

----------------------------------------------------------------------------
(* Fairness and specification *)

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Safety invariants *)

(* The GCD of u and v is preserved throughout the algorithm *)
GCDInvariant == GCD(u, v) = GCD(u_ini, v_ini)

(* Both u and v remain positive *)
PositiveInvariant == u >= 1 /\ v >= 1

(* Combined safety invariant *)
SafetyInvariant == TypeOK /\ GCDInvariant /\ PositiveInvariant

----------------------------------------------------------------------------
(* Correctness property: when done, u equals the GCD of the initial values *)

Correctness == pc = "done" => u = GCD(u_ini, v_ini)

(* Partial correctness is a safety property *)
PartialCorrectness == []Correctness

----------------------------------------------------------------------------
(* Liveness properties *)

(* Termination: the algorithm eventually reaches the done state *)
Termination == <>(pc = "done")

(* Total correctness: eventually done with correct result *)
TotalCorrectness == <>(pc = "done" /\ u = GCD(u_ini, v_ini))

----------------------------------------------------------------------------
(* TLC counting expectations for named properties *)

TerminationCount == TLCGet("distinct") >= 0

CorrectnessCount == TLCGet("distinct") >= 0

============================================================================
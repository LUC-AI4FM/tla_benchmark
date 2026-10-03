---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNumAssumption == MaxNum \in Nat /\ MaxNum >= 1

VARIABLES pc, u_ini, v_ini, u, v

vars == <<pc, u_ini, v_ini, u, v>>

(* Mathematical definition of GCD *)
Divides(p, n) == \E q \in Int : n = p * q

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(* Initial state *)
Init ==
    /\ pc = "start"
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u = u_ini
    /\ v = v_ini

(* Actions for Euclid's algorithm *)
Start ==
    /\ pc = "start"
    /\ pc' = "loop"
    /\ UNCHANGED <<u_ini, v_ini, u, v>>

Loop ==
    /\ pc = "loop"
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

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

(* Next state relation *)
Next == Start \/ Loop \/ Done

(* Specification with weak fairness *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Type invariant *)
TypeOK ==
    /\ pc \in {"start", "loop", "done"}
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u \in 1..(MaxNum * MaxNum)
    /\ v \in 1..(MaxNum * MaxNum)

(* Safety invariant: u and v remain positive *)
PositiveInvariant ==
    /\ u >= 1
    /\ v >= 1

(* Safety invariant: GCD is preserved *)
GCDInvariant ==
    GCD(u, v) = GCD(u_ini, v_ini)

(* Correctness: when done, u equals the GCD of initial values *)
PartialCorrectness ==
    pc = "done" => u = GCD(u_ini, v_ini)

(* Termination: the algorithm eventually terminates *)
Termination == <>(pc = "done")

(* Liveness: if not done, eventually make progress *)
Progress == pc = "loop" ~> (pc = "done" \/ u' # u \/ v' # v)

(* Result correctness property for TLC *)
ResultCorrect ==
    [](pc = "done" => u = v /\ u = GCD(u_ini, v_ini))

(* Named properties for TLC counting expectations *)
AlgorithmStarted == pc = "start"
AlgorithmInLoop == pc = "loop"
AlgorithmTerminated == pc = "done"
UGreaterThanV == pc = "loop" /\ u > v
VGreaterThanU == pc = "loop" /\ v > u
UEqualsV == pc = "loop" /\ u = v

==========================================================================
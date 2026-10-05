---------------------------- MODULE Euclid ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNum \in Nat /\ MaxNum >= 1

VARIABLES pc, u_ini, v_ini, u, v

vars == <<pc, u_ini, v_ini, u, v>>

----------------------------------------------------------------------------
(* Mathematical definition of GCD *)

Divides(p, n) == \E q \in Int : n = p * q

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

----------------------------------------------------------------------------
(* PlusCal algorithm (in comments):

--algorithm Euclid
variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u = u_ini, v = v_ini;
begin
  loop:
    while u /= v do
      if u > v then
        u := u - v;
      else
        v := v - u;
      end if;
    end while;
  done:
    skip;
end algorithm;

*)

----------------------------------------------------------------------------
(* TLA+ translation of the PlusCal algorithm *)

Init ==
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u = u_ini
    /\ v = v_ini
    /\ pc = "loop"

Loop ==
    /\ pc = "loop"
    /\ IF u /= v
       THEN /\ IF u > v
               THEN /\ u' = u - v
                    /\ v' = v
               ELSE /\ v' = v - u
                    /\ u' = u
            /\ pc' = "loop"
            /\ UNCHANGED <<u_ini, v_ini>>
       ELSE /\ pc' = "done"
            /\ UNCHANGED <<u_ini, v_ini, u, v>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Loop
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

----------------------------------------------------------------------------
(* Type Invariant *)

TypeOK ==
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u \in 1..MaxNum
    /\ v \in 1..MaxNum
    /\ pc \in {"loop", "done"}

----------------------------------------------------------------------------
(* Safety Invariants *)

(* The GCD of u and v is always equal to the GCD of the initial values *)
GCDInvariant ==
    GCD(u, v) = GCD(u_ini, v_ini)

(* u and v are always positive *)
PositiveInvariant ==
    u >= 1 /\ v >= 1

----------------------------------------------------------------------------
(* Correctness Property *)

(* When the algorithm terminates, u equals the GCD of the initial values *)
Correctness ==
    pc = "done" => u = GCD(u_ini, v_ini)

----------------------------------------------------------------------------
(* Liveness Properties *)

(* The algorithm eventually terminates *)
Termination ==
    <>(pc = "done")

(* The algorithm eventually computes the correct GCD *)
EventuallyCorrect ==
    <>(pc = "done" /\ u = GCD(u_ini, v_ini))

----------------------------------------------------------------------------
(* TLC Counting Expectations *)

CountTerminated == pc = "done"

CountInLoop == pc = "loop"

CountUGreaterV == pc = "loop" /\ u > v

CountVGreaterU == pc = "loop" /\ v > u

CountEqual == u = v

============================================================================
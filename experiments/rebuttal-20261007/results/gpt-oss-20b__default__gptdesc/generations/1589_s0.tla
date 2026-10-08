MODULE Euclid
EXTENDS Integers

CONSTANT MaxNum \* positive integer upper bound

VARIABLES pc, u_ini, v_ini, u, v, stepCount

(* Define GCD function *)
GCD(x, y) == 
    IF x = 0 THEN y
    ELSE IF y = 0 THEN x
    ELSE LET r == Mod(x, y) IN GCD(y, r)

Init ==
    /\ pc = "Start"
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u = u_ini
    /\ v = v_ini
    /\ stepCount = 0

Next ==
    \/ /\ pc = "Start"
       /\ pc' = "Loop"
       /\ UNCHANGED <<u, v, u_ini, v_ini, stepCount>>
    \/ /\ pc = "Loop"
       /\ (u > v)
       /\ u' = u - v
       /\ pc' = "Loop"
       /\ stepCount' = stepCount + 1
       /\ UNCHANGED <<v, u_ini, v_ini>>
    \/ /\ pc = "Loop"
       /\ (v > u)
       /\ v' = v - u
       /\ pc' = "Loop"
       /\ stepCount' = stepCount + 1
       /\ UNCHANGED <<u, u_ini, v_ini>>
    \/ /\ pc = "Loop"
       /\ (u = v)
       /\ pc' = "Done"
       /\ UNCHANGED <<u, v, u_ini, v_ini, stepCount>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<pc, u, v, u_ini, v_ini, stepCount>>

vars == <<pc, u_ini, v_ini, u, v, stepCount>>

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

(* Safety invariant: when done, u equals v and equals GCD of initial values *)
Correctness ==
    (pc = "Done") => (u = v) /\ (u = GCD(u_ini, v_ini))

SafetyInvariant == Correctness

(* Liveness property: algorithm eventually terminates *)
Termination ==
    <> (pc = "Done")

(* Counting expectation for stepCount *)
\* @expectation StepCount = 0
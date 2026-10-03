---------------------------- MODULE Euclid --------------------------------
EXTENDS Integers, TLC

CONSTANT MaxNum

VARIABLE pc, u_ini, v_ini, u, v

Spec == 
  (pc = "Init") /\ (u_ini \in 1..MaxNum) /\ (v_ini \in 1..MaxNum) /\ 
  (u = u_ini) /\ (v = v_ini)

Next == 
  IF pc = "Init" THEN
    pc' = "Loop" /\ u' = u_ini /\ v' = v_ini
  ELSE IF pc = "Loop" THEN
    IF u' = 0 THEN 
      pc' = "Done" /\ v' = v
    ELSE IF v' = 0 THEN 
      pc' = "Done" /\ u' = u
    ELSE IF u > v THEN 
      pc' = "Loop" /\ u' = u - v /\ v' = v
    ELSE 
      pc' = "Loop" /\ u' = u /\ v' = v - u
  ELSE 
    UNCHANGED <<pc, u, v>>

Termination == <>(pc = "Done")

Invariant == (u_ini \in 1..MaxNum) /\ (v_ini \in 1..MaxNum) /\ 
             (u \in 0..MaxNum) /\ (v \in 0..MaxNum)

THEOREM Spec => []Termination
THEOREM Spec => [](pc = "Done" => GCD(u_ini, v_ini) = v)
=============================================================================
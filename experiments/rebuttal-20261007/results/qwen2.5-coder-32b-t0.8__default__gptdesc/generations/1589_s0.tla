------------------------------ MODULE EuclideanAlgorithm ------------------------------

EXTENDS Naturals, TLC

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

(*--algorithm euclid
variables u = u_ini, v = v_ini;
begin
    while (u /= v) do
        if (u > v) then
            u := u - v
        else
            v := v - u
end algorithm*)

Init == 
  /\ pc = "start"
  /\ \E x \in 1..MaxNum : u_ini = x
  /\ \E y \in 1..MaxNum : v_ini = y
  /\ u = u_ini
  /\ v = v_ini

Next ==
  \/ /\ pc = "start"
     /\ pc' = "while_check"
  \/ /\ pc = "while_check"
     /\ (u # v)
     /\ pc' = "if_cond"
  \/ /\ pc = "while_check"
     /\ (u = v)
     /\ pc' = "done"
  \/ /\ pc = "if_cond"
     /\ (u > v)
     /\ u' = u - v
     /\ pc' = "while_check"
  \/ /\ pc = "if_cond"
     /\ (u <= v)
     /\ v' = v - u
     /\ pc' = "while_check"

Spec ==
  /\ Init
  /\ [][Next]_<<pc, u, v>>
  /\ WF_next(<<pc, u, v>>, Next)

(* Correctness and Termination *)
Terminated == pc = "done"
FinalResult == (u = GCD(u_ini, v_ini))

GCD(a, b) ==
    LET recGCD(x, y) ==
        IF y = 0 THEN x
        ELSE recGCD(y, x \mod y)
    IN recGCD(a, b)

Inv ==
  /\ u \in 1..MaxNum
  /\ v \in 1..MaxNum

SpecCorrect ==
  Spec /\ []<>Terminated /\ <>[]FinalResult

<< proved >> TLCGetAssumption(Terminated)
<< proved >> TLCGetAssumption(FinalResult)

=============================================================================
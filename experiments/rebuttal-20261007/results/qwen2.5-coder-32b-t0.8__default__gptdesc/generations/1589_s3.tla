------------------------------ MODULE EuclidGCD ------------------------------

EXTENDS Integers, TLC

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

(*--algorithm euclid_gcd
begin
    with u := u_ini, v := v_ini do
        while u /= v do
            if u > v then
                u := u - v;
            else
                v := v - u;
            end if;
        end while;
    end with;
end algorithm *)

Init == /\ pc = "start"
       /\ \/ pc = "done"
       /\ 1 <= u_ini <= MaxNum
       /\ 1 <= v_ini <= MaxNum
       /\ u = u_ini
       /\ v = v_ini

Next ==
   CASE pc = "start" -> /\ u > v
                           /\ u' = u - v
                           /\ v' = v
                           /\ pc' = "start"
          [] u > v ->     /\ u' = u - v
                           /\ v' = v
                           /\ pc' = "start"
          [] u < v ->     /\ u' = u
                           /\ v' = v - u
                           /\ pc' = "start"
          [] u = v ->     /\ u' = u
                           /\ v' = v
                           /\ pc' = "done"

Spec ==
  WF_pc(Next) /\
  Init /\ [][ Next ]_<<pc>>

(* Fairness *)
WF_pc(action) == <>(/\ action
                  /\ [](action => <>(~action)))

(* Correctness Property *)
CorrectResult == u = v /\ GCD(u_ini, v_ini) = u

(* TLC Expectations *)
CountInitStates ==
  LET InitStates \in {s \in [pc \in {"start", "done"}, u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u \in 1..MaxNum, v \in 1..MaxNum] : s \in Init}
  IN TLCGetSetSize(InitStates)

CountCorrectResults ==
  LET CorrectStates \in {s \in [pc \in {"start", "done"}, u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u \in 1..MaxNum, v \in 1..MaxNum] : s \in Spec /\ pc = "done" /\ CorrectResult}
  IN TLCGetSetSize(CorrectStates)

=============================================================================
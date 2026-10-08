------------------------------- MODULE EuclidGCD ------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

(*--algorithm euclid_gcd
begin
    with (u := u_ini; v := v_ini)
    while u /= v do
        if u > v then
            u := u - v;
        else
            v := v - u;
        end if;
    end while;
end algorithm *)

Init == /\ pc = "with"
         /\ \/ u_ini \in 1..MaxNum
         /\ \/ v_ini \in 1..MaxNum
         /\ u = u_ini
         /\ v = v_ini

Next ==
   \/ /\ pc = "with"
      /\ pc' = "while"
      /\ u' = u
      /\ v' = v
   \/ /\ pc = "while"
      /\ u # v
      /\ \/ /\ u > v
             /\ pc' = "while"
             /\ u' = u - v
             /\ v' = v
         \/ /\ u <= v
             /\ pc' = "while"
             /\ u' = u
             /\ v' = v - u
   \/ /\ pc = "while"
      /\ u = v
      /\ pc' = "end"

Spec ==
  WF_pc(Next) /\
  Init /\ [][Next]_<<pc>>

GCD(a, b) == CHOOSE d \in 1..a: \A k \in 1..b: (k \divides a) => (k \divides d)

CorrectResult == u = v => u = GCD(u_ini, v_ini)

Termination == <>[](pc # "end") => <>(pc = "end")

Liveness ==
  Termination

Invariants ==
  /\ \/ pc = "with"
     \/ pc = "while"
     \/ pc = "end"
  /\ u \in 1..MaxNum
  /\ v \in 1..MaxNum

====
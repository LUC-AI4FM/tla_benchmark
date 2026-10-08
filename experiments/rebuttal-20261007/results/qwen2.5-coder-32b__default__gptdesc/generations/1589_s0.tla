------------------------------- MODULE EuclidGCD -------------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

(*--algorithm euclid_gcd
variables u = u_ini, v = v_ini;
begin
    while (u /= v) do
        if (u > v)
            then u := u - v;
        else
            v := v - u;
end algorithm *)

Init == /\ pc = "start"
        /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ u = u_ini
        /\ v = v_ini

Next ==
    \/ /\ pc = "start"
       /\ u > v
       /\ pc' = "u_minus_v"
       /\ u' = u - v
       /\ v' = v
       /\ u_ini' = u_ini
       /\ v_ini' = v_ini
    \/ /\ pc = "start"
       /\ u <= v
       /\ pc' = "v_minus_u"
       /\ u' = u
       /\ v' = v - u
       /\ u_ini' = u_ini
       /\ v_ini' = v_ini
    \/ /\ pc \in {"u_minus_v", "v_minus_u"}
       /\ u = v
       /\ pc' = "done"
       /\ u' = u
       /\ v' = v
       /\ u_ini' = u_ini
       /\ v_ini' = v_ini

Spec ==
    /\ Init
    /\ [][Next]_<<pc, u, v>>
    /\ WF_next(<<pc, u, v>>, Next)

GCD(a, b) == CHOOSE d \in 1..Min(a, b) : \A k \in 1..a \cup 1..b : (k \divides a => k \divides b => k \leq d)

Termination ==
    <>[](pc = "done")

Correctness ==
    [](pc = "done" => GCD(u_ini, v_ini) = u)

====
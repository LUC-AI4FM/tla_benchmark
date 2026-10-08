------------------------------- MODULE EuclidGCD -------------------------------

EXTENDS Naturals, Sequences

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

(*--algorithm EuclidGCD
variables u = u_ini, v = v_ini;
begin
E1: while (u /= v) do
    if (u > v) then
        u := u - v;
    else
        v := v - u;
    end if;
end while;
end algorithm *)

Init == /\ pc = "E1"
        /\ \/ /\ u_ini \in 1..MaxNum
               /\ v_ini \in 1..MaxNum
               /\ u = u_ini
               /\ v = v_ini

Next ==
    \/ /\ pc = "E1"
       /\ u # v
       /\ (\/ /\ u > v
              /\ u' = u - v
              /\ v' = v
              /\ pc' = "E1"
             \/ /\ u <= v
                /\ u' = u
                /\ v' = v - u
                /\ pc' = "E1")
    \/ /\ pc = "E1"
       /\ u = v
       /\ UNCHANGED <<u_ini, v_ini, u, v>>
       /\ pc' = "Done"

Spec ==
    /\ Init
    /\ [][Next]_<<pc, u_ini, v_ini, u, v>>
    /\ WF_next(<<pc, u_ini, v_ini, u, v>>, Next)

GCD(a, b) == CHOOSE d \in 1..Min(a,b) : \/ a % d = 0
                                          /\ b % d = 0
                                          /\ \A e \in 1..Min(a,b) : (a % e = 0 /\ b % e = 0) => e <= d

Termination == <>[](pc = "Done")

Correctness == GCD(u_ini, v_ini) = u

Expect <<GCD(u_ini, v_ini), u>>

=============================================================================
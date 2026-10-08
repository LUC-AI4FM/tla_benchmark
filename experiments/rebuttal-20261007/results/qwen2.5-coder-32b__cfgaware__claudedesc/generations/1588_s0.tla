------------------------------- MODULE EuclidGCD -------------------------------

CONSTANTS N \* Bounded range for v

VARIABLES pc, u, v, v_ini

(*--algorithm euclid_gcd
variables 
    pc = "lp",
    u = 24,
    v \in 1..N,
    v_ini = v;

begin
lp: while (u # 0) do
        if (u < v) then
            /\ u := v;
            /\ v := pc_old.u;
        end if;
        pc := "a";
    a:
        /\ u := u - v;
        /\ pc := "lp";
    end while;
    print(v);
    pc := "Done";
Terminating: do
    skip;
end algorithm *)

\* Reference GCD function
GCD(a, b) == 
    LET RecGCD(x, y) ==
        IF y = 0 THEN x ELSE RecGCD(y, x \% y)
    IN RecGCD(a, b)

Next == \/ /\ pc = "lp"
             /\ (u # 0)
             /\ (IF u < v THEN
                    /\ u' = v
                    /\ v' = u
                 ELSE
                    /\ u' = u
                    /\ v' = v
                 )
             /\ pc' = "a"
         \/ /\ pc = "a"
             /\ u' = u - v
             /\ pc' = "lp"
         \/ /\ pc = "lp"
             /\ u = 0
             /\ pc' = "Done"

Spec == /\ PCInit
        /\ [][Next]_<<pc, u, v>>
        /\ WF_next(<<pc, u, v>>)

PCInit == /\ pc = "lp"
          /\ u = 24
          /\ v \in 1..N
          /\ v_ini = v

Termination == <>(pc = "Done")

=============================================================================
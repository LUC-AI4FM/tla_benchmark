------------------------------- MODULE EuclidGCD -------------------------------

CONSTANTS MaxNum \* = 20

VARIABLES pc, u, v, u_ini, v_ini

(*--algorithm euclid_gcd
variables pc = "a", u, v, u_ini, v_ini;

begin
    Init:
        with (u = u_ini; v = v_ini);
    
    a:
        if u # 0 then
            if u < v then
                /\ u := v;
                /\ v := u_old;
                /\ pc := "b";
            else
                pc := "b";
            end if;
        else
            assert(v = GCD(u_ini, v_ini));
            pc := "Done";
        end if;

    b:
        with (u = u - v);
        pc := "a";

end algorithm;*)

GCD(x, y) == CHOOSE d \in {d \in 1..MIN(x, y): x % d = 0 /\ y % d = 0}: UNCHANGED <<x, y>>

Next ==
    \/ /\ pc = "a"
       /\ (u # 0 -> \/ /\ u < v
                           /\ u' = v
                           /\ v' = u
                           /\ pc' = "b"
                      \/ /\ u >= v
                         /\ pc' = "b")
       /\ (u = 0 -> /\ v = GCD(u_ini, v_ini)
                     /\ pc' = "Done")
    \/ /\ pc = "b"
       /\ u' = u - v
       /\ pc' = "a"

Spec ==
    /\ Init
    /\ [][Next]_<<pc, u, v>>
    /\ WF_next(Next)

Init == 
    /\ pc = "a"
    /\ \E i \in 1..MaxNum : \E j \in 1..MaxNum : u_ini = i /\ v_ini = j
    /\ u = u_ini
    /\ v = v_ini

Termination ==
    <>[](pc = "Done")

Invariant ==
    [](pc = "Done" -> v = GCD(u_ini, v_ini))

Finished == pc = "Done"
SwapOccurs == \/ pc = "a" /\ u < v

PossibleCounts ==
    /\ TLCGet("States") = 800
    /\ TLCGet("Transitions") = 698

=============================================================================
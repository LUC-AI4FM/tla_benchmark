------------------------------- MODULE EuclidGCD -------------------------------

CONSTANTS
    \* No additional constants are needed for this specification

VARIABLES
    u, v, pc

(*--algorithm euclid_gcd
variables u = 24, v \in 1..50, pc = "Lbl_1"

Lbl_1:
    print <<u, v>>;
    pc := "Lbl_2";

Lbl_2:
    while u # 0 do
        if u < v then
            temp := u;
            u := v;
            v := temp;
        end if;
        pc := "Lbl_3";
        
Lbl_3:
        u := u - v;
        pc := "Lbl_2";
    end while;
    
    pc := "Done";

end algorithm *)

Init == /\ u = 24
        /\ v \in 1..50
        /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ pc' = "Lbl_2"

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ \/ /\ u # 0
           /\ (\/ /\ u >= v
                  /\ u' = u - v
              \/ /\ u < v
                 /\ u' = v
                 /\ v' = u)
           /\ pc' = "Lbl_2"
       \/ /\ u = 0
          /\ pc' = "Done"

Lbl_3 ==
    /\ pc = "Lbl_3"
    /\ UNCHANGED <<u, v>>
    /\ pc' = "Lbl_2"

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ (pc # "Done" => FALSE)

Spec == Init /\ [][Next]_<<u, v, pc>>

=============================================================================
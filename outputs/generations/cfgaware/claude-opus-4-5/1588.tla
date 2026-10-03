---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

(*--algorithm Euclid
variables u = 24, v \in 1..N, v_ini = v;

begin
Loop:
    while u # 0 do
        if u < v then
            u := v || v := u;
        end if;
    Subtract:
        u := u - v;
    end while;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "7a5c5f5a" /\ chksum(tla) = "3b5f5f5a")
VARIABLES u, v, v_ini, pc

vars == << u, v, v_ini, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF u # 0
              THEN /\ IF u < v
                         THEN /\ /\ u' = v
                                 /\ v' = u
                         ELSE /\ TRUE
                              /\ UNCHANGED << u, v >>
                   /\ pc' = "Subtract"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << u, v >>
        /\ v_ini' = v_ini

Subtract == /\ pc = "Subtract"
            /\ u' = u - v
            /\ pc' = "Loop"
            /\ UNCHANGED << v, v_ini >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Loop \/ Subtract
           \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

==========================================================================
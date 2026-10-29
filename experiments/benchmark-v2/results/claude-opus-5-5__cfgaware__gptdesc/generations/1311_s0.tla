---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

(* --algorithm Euclid
variables u = 24, v \in 1 .. 50;
begin
a: while u # 0 do
     d: if u < v then
          u := v || v := u;
        end if;
     f: u := u - v;
   end while;
end algorithm
*)

VARIABLES u, v, pc

vars == << u, v, pc >>

Init == /\ u = 24
        /\ v \in 1 .. 50
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF u # 0
           THEN /\ pc' = "d"
           ELSE /\ pc' = "Done"
     /\ UNCHANGED << u, v >>

d == /\ pc = "d"
     /\ IF u < v
           THEN /\ u' = v
                /\ v' = u
           ELSE /\ TRUE
                /\ UNCHANGED << u, v >>
     /\ pc' = "f"

f == /\ pc = "f"
     /\ u' = u - v
     /\ pc' = "a"
     /\ v' = v

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ d \/ f
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars

Termination == <>(pc = "Done")

=============================================================================
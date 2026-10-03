------------------------------- MODULE EuclidAlgorithm -------------------------------

CONSTANTS N

VARIABLES u, v, v_ini, pc

(*--algorithm Euclid
variables u = 24, v \in 1..N;
begin
    while (u # v) do
        if (u > v) then
            u := u - v;
        else
            v := v - u;
        end if;
    end while;
end algorithm*)

\* BEGIN TRANSLATION
Spec ==
  /\ TYPEOK
  /\ Init
  /\ [][Next]_<<u, v, v_ini, pc>>
  /\ WF_next(<<u, v, v_ini, pc>>)

Init ==
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v
  /\ pc = "start"

Next ==
  \/ /\ pc = "start"
     /\ u # v
     /\ (/\ u > v
         /\ u' = u - v
         /\ v' = v
         /\ v_ini' = v_ini
         /\ pc' = "start")
        \/ (/\ u <= v
            /\ u' = u
            /\ v' = v - u
            /\ v_ini' = v_ini
            /\ pc' = "start")
  \/ /\ pc = "start"
     /\ u = v
     /\ u' = u
     /\ v' = v
     /\ v_ini' = v_ini
     /\ pc' = "Done"

WF_next(vars) ==
  \A vars \in Init : <<vars>> \in WF_vars(Next)

Termination ==
  <>[](pc = "Done")

TYPEOK ==
  /\ u \in Nat
  /\ v \in Nat
  /\ v_ini \in Nat
  /\ pc \in {"start", "Done"}

\* END TRANSLATION

=============================================================================
---- MODULE FischerTimed ----
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon, Infinity

VARIABLES state, flag, timer, cs

(* --algorithm FischerTimed
   CONSTANTS N, Delta, Epsilon, Infinity

   VARIABLE state, flag, timer, cs

   Init == 
     /\ state = [i \in 1..N |-> 0]      \* StateNC
     /\ flag = [i \in 1..N |-> FALSE]
     /\ timer = [i \in 1..N |-> Infinity]
     /\ cs   = [i \in 1..N |-> FALSE]

   Tick == 
     /\ UNCHANGED <<state, flag, cs>>
     /\ timer' = [timer EXCEPT ![i] =
           IF timer[i] = Infinity THEN Infinity
              ELSE IF timer[i] > 0 THEN timer[i] - Epsilon
                   ELSE 0
           FORALL i \in 1..N]

   Process(i) ==
     IF state[i] = 0 THEN
       flag[i] := TRUE;
       timer[i] := Delta;
       state[i] := 1;          \* StateTRY
     ELSIF state[i] = 1 THEN
       IF timer[i] <= 0 /\ (\A j \in 1..N : j # i => flag[j] = FALSE) THEN
         cs[i] := TRUE;
         state[i] := 2;        \* StateCS
       ENDIF;
     ELSIF state[i] = 2 THEN
       cs[i] := FALSE;
       flag[i] := FALSE;
       state[i] := 0;
     ENDIF

   Next == \/ Tick \/ \E i \in 1..N : Process(i)

--* )

MutualExclusion == 
  \A i, j \in 1..N :
    i # j => ~(cs[i] /\ cs[j])

Spec == Init /\ [][Next]_<<state, flag, timer, cs>> /\ MutualExclusion

Liveness == [] <> (\E i \in 1..N : cs[i])
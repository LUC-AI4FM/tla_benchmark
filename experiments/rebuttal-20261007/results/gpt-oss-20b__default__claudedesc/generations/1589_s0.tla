MODULE EuclidGCD
EXTENDS TLC

CONSTANTS MaxNum, u_ini, v_ini

ASSUME MaxNum = 20

VARIABLES pc, u, v

Init ==
    /\ u = u_ini
    /\ v = v_ini
    /\ pc = "a"

Largest(dSet) == CHOOSE d \in dSet : \A e \in dSet : e <= d

GCD(x,y) == Largest({d \in 1..x : (x MOD d = 0) /\ (y MOD d = 0)})

a ==
    /\ pc = "a"
    /\ IF u # 0 THEN
           /\ IF u < v THEN
                  /\ u' = v
                  /\ v' = u
              ELSE
                  /\ u' = u
                  /\ v' = v
           /\ pc' = "b"
       ELSE
           /\ u' = u
           /\ v' = v
           /\ pc' = "Done"

b ==
    /\ pc = "b"
    /\ u' = u - v
    /\ v' = v
    /\ pc' = "a"

Next == a \/ b

Spec == Init /\ WF_ <<u,v,pc>> (Next)

Invariant ==
    /\ pc = "Done" => v = GCD(u_ini, v_ini)

Termination == <> (pc = "Done")

\* @coverage Finished
Finished == pc = "Done"

\* @coverage SwapOccurs
SwapOccurs == /\ pc = "a" /\ u # 0 /\ u < v

THEOREM PossibleCounts ==
    Coverage(Finished) = 800
    /\ Coverage(SwapOccurs) = 698

===============================================================================
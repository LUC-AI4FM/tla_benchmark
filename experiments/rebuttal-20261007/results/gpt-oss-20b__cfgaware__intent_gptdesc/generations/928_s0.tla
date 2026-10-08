MODULE Clock

VARIABLES h

(* Initial state: any valid hour 1..12 *)
Init == h \in 1..12

(* Stepwise increment-or-wrap transition *)
HC == [h' = IF h = 12 THEN 1 ELSE h + 1]

(* Modular arithmetic alternative *)
HC2 == [h' = ((h MOD 12) + 1)]

(* Deterministic next-state relation *)
Next == HC

(* Complete specification *)
Spec == Init /\ [][Next]_h

(* Safety property: always a valid hour *)
Safety == \Box (h \in 1..12)

(* Liveness property: each hour appears infinitely often *)
Liveness == \A i \in 1..12 : \Box \Diamond (h = i)

(* Equivalence of the two transition formulations *)
EquivProp == \A h,h' : (HC <=> HC2)

THEOREM Equivalence == EquivProp
THEOREM SafetyTheorem == Spec => Safety
THEOREM LivenessTheorem == Spec => Liveness

===============================================================================
MODULE Clock12
EXTENDS Naturals
VARIABLES hr

(* Initial condition *)
HCini == hr ∈ 1..12

(* Next-state relation: advance hour by one with wrap *)
HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

(* Allow stuttering steps where hr remains unchanged *)
Next == HCnxt \/ (hr' = hr)

(* Full specification *)
HC == HCini /\ []Next

THEOREM ClockInvariant == HC => []HCini

SPECIFICATION HC
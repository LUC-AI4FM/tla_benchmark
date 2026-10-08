------------------------------ MODULE Clock ------------------------------
EXTENDS Naturals

VARIABLE hour

(* -- Initial condition ----------------------------------------------------- *)
Init == hour ∈ 1..12

(* -- Next-state relation --------------------------------------------------- *)
Next ==
  /\ hour' = IF hour = 12 THEN 1 ELSE hour + 1

(* -- Fairness condition: ensure infinitely many advancing steps --------- *)
AlwaysTick == WF_vars(Next)

(* -- Temporal specification combining Init, Next and fairness ---------- *)
LSpec == Init /\ [][Next]_hour /\ AlwaysTick

(* -- Invariant that the hour always stays within 1..12 ------------------- *)
AllTimes == [] (hour ∈ 1..12)

(* -- Theorem: type invariance ------------------------------------------------- *)
THEOREM TypeInvariance ==
  LSpec => AllTimes

(* -- Theorem: infinitely many advancing steps occur ------------------------ *)
THEOREM InfiniteAdvancingSteps ==
  LSpec => AlwaysTick

(* -- Theorem: each hour value appears infinitely often --------------------- *)
THEOREM EachHourInfinitelyOften ==
  LSpec =>
    []<>(hour = 1) /\ []<>(hour = 2) /\ []<>(hour = 3) /\ []<>(hour = 4) \
    []<>(hour = 5) /\ []<>(hour = 6) /\ []<>(hour = 7) /\ []<>(hour = 8) \
    []<>(hour = 9) /\ []<>(hour =10) /\ []<>(hour =11) /\ []<>(hour =12)

=============================================================================
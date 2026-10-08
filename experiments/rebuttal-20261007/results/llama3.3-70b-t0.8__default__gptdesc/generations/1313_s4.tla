```
MODULE DieHardWaterJug
EXTENDS Integers, TLC
CONSTANTS CapSmall, CapBig
VARIABLES small, big, waterUsage, steps

Init == (small = 0) ∧ (big = 0) ∧ (waterUsage = 0) ∧ (steps = 0)

Next == 
  ∨ (∃ s ∈ {1, 2} ∩ {small < CapSmall, big < CapBig} : 
        CASE s = 1 → small' = CapSmall
        [] s = 2 → big' = CapBig
        END ∧ waterUsage' = waterUsage + 1 ∧ steps' = steps + 1 ∧ big' = big)
  ∨ (∃ s ∈ {1, 2} ∩ {small > 0, big > 0} : 
        CASE s = 1 → small' = 0
        [] s = 2 → big' = 0
        END ∧ waterUsage' = waterUsage ∧ steps' = steps + 1 ∧ big' = big)
  ∨ (∃ s ∈ {1, 2} ∩ {small > 0, CapBig - big > 0} : 
        CASE s = 1 → small' = small - (CapBig - big) ∧ big' = CapBig
        [] s = 2 → small' = 0 ∧ big' = big + small
        END ∧ waterUsage' = waterUsage ∧ steps' = steps + 1)
  ∨ (∃ s ∈ {1, 2} ∩ {big > 0, CapSmall - small > 0} : 
        CASE s = 1 → big' = big - (CapSmall - small) ∧ small' = CapSmall
        [] s = 2 → big' = 0 ∧ small' = small + big
        END ∧ waterUsage' = waterUsage ∧ steps' = steps + 1)
  ∨ (small' = small) ∧ (big' = big) ∧ (waterUsage' = waterUsage) ∧ (steps' = steps + 1)

Spec == Init ∧ [][Next]_<<small, big, waterUsage, steps>>
THEOREM Spec => []<>(big = 4)
THEOREM Spec => <>(waterUsage > 10)
ModelCheck == Spec ∧ small ∈ 0..CapSmall ∧ big ∈ 0..CapBig
Stats == <<steps, waterUsage>>
```
Note: The values of `CapSmall` and `CapBig` should be set to the desired capacities (3 and 5 respectively) when model checking with TLC.
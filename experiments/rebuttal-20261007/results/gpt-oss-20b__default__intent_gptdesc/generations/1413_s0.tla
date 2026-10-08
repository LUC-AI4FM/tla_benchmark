MODULE PersistentTautology
EXTENDS Naturals

VARIABLE val

Init == val = TRUE

Next == val' = val

Spec == Init /\ [] Next

SafetyInvariant == val = TRUE

LivenessProperty == \A p \in {TRUE, FALSE} : (<>p => <>[]p)

THEOREM ReachStable == LivenessProperty
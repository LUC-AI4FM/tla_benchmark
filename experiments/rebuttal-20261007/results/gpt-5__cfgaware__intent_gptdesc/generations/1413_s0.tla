---- MODULE PersistentTautology ----

VARIABLES val

Init == val = TRUE

Next == UNCHANGED val

Spec == Init /\ []Next

AlwaysTrue == val

TautologyStabilizes == (<>AlwaysTrue) => (<>[]AlwaysTrue)

THEOREM Spec => TautologyStabilizes

====
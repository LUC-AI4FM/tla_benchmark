MODULE RandomFunctionSample

DOMAIN == 1..9
CODOMAIN == {"a","b","c","d","e","f","g","h","i","j"}

VARIABLE sample

Init ==
    sample = RandomSubset(DOMAIN -> CODOMAIN, 1000)

Next ==
    UNCHANGED sample

Inv ==
    (#sample = 1000) /\ (sample \subseteq DOMAIN -> CODOMAIN)

Spec ==
    Init
    /\ [][Next]_sample
    /\ []Inv

===============================================================================
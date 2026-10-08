---------------------------- MODULE CounterSystem ----------------------------

EXTENDS Integers

CONSTANTS \\
    /\ InitOuter
    /\ NextOuter
    /\ SpecOuter
    /\ InnerSpec
    /\ InnerInit
    /\ InnerNext

VARIABLES outerX

MODULE InnerModule
    VARIABLE x
    VARIABLES <<x>>

    InnerInit == x = 0
    InnerNext == \/ (x < 3) -> \E _ : x' = x + 1
                 \/ TRUE     -> x' = x
    InnerSpec == SPECIFICATION InitOuter /\ [][InnerNext]_<<x>> /\ WF_x(InnerNext)
END MODULE

InitOuter == outerX = 0

NextOuter ==
    \/ INSTANCE InnerModule WITH x <- outerX, <<x>> <- <<outerX>>
    \/ (/\ ~(outerX < 3) 
        -> UNCHANGED outerX)

SpecOuter ==
    SPECIFICATION InitOuter /\ [][NextOuter]_<<outerX>> /\ SF_x(NextOuter)

THEOREM SpecOuter => [](<>[outerX = 3]))

=============================================================================
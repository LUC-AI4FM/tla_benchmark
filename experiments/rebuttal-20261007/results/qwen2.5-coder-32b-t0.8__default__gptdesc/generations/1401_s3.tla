---------------------------- MODULE CounterSystem ----------------------------
EXTENDS Naturals, TLC

CONSTANTS x
VARIABLES outerX

MODULE InnerModule
    VARIABLES x

    Init == x = 0

    Next ==
        \/ /\ x < 3
           /\ x' = x + 1
        \/ /\ TRUE
           /\ x' = x

    WF_x <<Next>> == <>[](x < 3 => <>[]<<x' = x + 1>>)

ENDMODULE

VARIABLES outerX

Init == outerX = 0

InnerStep ==
    INSTANCE InnerModule WITH x <- outerX, x' <- outerX'

Next ==
    \/ /\ InnerModule!Next
       /\ outerX' = InnerModule!x'
    \/ /\ ~InnerModule!Next
       /\ outerX' = outerX

WF_outerX <<Next>> == <>[](outerX < 3 => <>[]<<outerX' = outerX + 1>>)

Spec ==
    Init /\ [][Next]_<<outerX>>
        /\ WF_x
        /\ WF_outerX
        /\ <><<>(outerX = 3)>

================================================================================
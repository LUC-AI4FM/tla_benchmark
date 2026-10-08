------------------------------ MODULE Outer ------------------------------
EXTENDS Sequences

MODULE Inner
    EXTENDS Sequences
    VARIABLES result, seq
    Init == result = 0 /\ seq = <<1,2,3>>
    InnerStep ==
        /\ result = 0
        /\ result' = 1
        /\ seq' = Filter(seq, x # 1)
END MODULE

INSTANCE Inner AS IM WITH result -> result, seq -> seq

VARIABLES result, seq

vars == <<result, seq>>

InitOuter == result = 0 /\ seq = <<1,2,3>>

Next ==
    IM.InnerStep
    \/ (result' = result /\ seq' = seq)

Spec == InitOuter /\ [][Next]_vars /\ WF_IM.InnerStep

SpecRunsToEnd == <> (¬Enabled(IM.InnerStep) /\ [](¬Enabled(IM.InnerStep)))

====
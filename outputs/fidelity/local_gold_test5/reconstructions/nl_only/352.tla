MODULE RegressionTest

EXTENDS TLC, Sequences, FiniteSets

CONSTANTS 
    Domain \* A finite set used for domain-bound functions

VARIABLES x

Init == x = TRUE

Next == UNCHANGED x

\* Define some sample functions and records for testing
ConstFun == [d \in Domain |-> 42]
IdFun == [d \in Domain -> d]
TupleFun == [t \in DOMAIN {<<a, b>> \in [Domain -> BOOLEAN] : <<a, b>>}]
RecordFun == [r \in DOMAIN {rec : [x: BOOLEAN, y: BOOLEAN]} : rec.x]

\* Test function application and updates
Inv ==
    LET 
        sampleTuple == <<TRUE, FALSE>>
        sampleRecord == [x |-> TRUE, y |-> FALSE]
        updatedRecord == [sampleRecord EXCEPT !.y := TRUE]
        anonFun == (a, b) -> a /\ b
        nestedTuple == <<sampleTuple, sampleTuple>>
    IN
    /\ Assert(ConstFun[CHOOSE d \in Domain] = 42)
    /\ Assert(IdFun[CHOOSE d \in Domain] = CHOOSE d \in Domain)
    /\ Assert(TupleFun[sampleTuple] = sampleTuple)
    /\ Assert(RecordFun[sampleRecord] = TRUE)
    /\ Assert(updatedRecord.y = TRUE)
    /\ Assert(anonFun[TRUE, FALSE] = FALSE)
    /\ Assert(nestedTuple[1][2] = FALSE)

Spec == Init /\ [][Next]_<<x>> /\ WF_next(<<x>>) /\ Inv
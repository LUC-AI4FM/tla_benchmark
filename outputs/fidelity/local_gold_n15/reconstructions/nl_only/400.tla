---- MODULE TestLETExpressions ----

EXTENDS Integers, Sequences, TLC

CONSTANTS Domain

VARIABLES x

Init == x = 0

Next == TRUE

FcnSubst(f, dom, g) == [d \in dom |-> f[d] + g[d]]

Inv ==
    LET emptySet == {}
        trivialFunction == [e \in emptySet |-> 0]
        seqLikeFunction == <<1, 2, 3>>
        incrementedSeq == FcnSubst(seqLikeFunction, DOMAIN seqLikeFunction, [d \in DOMAIN seqLikeFunction |-> 1])
    IN
        /\ Print(Tuple("emptySet:", emptySet))
        /\ Assert(emptySet = {}, "Expected an empty set")
        /\ Print(Tuple("trivialFunction:", trivialFunction))
        /\ Assert(trivialFunction = [e \in {} |-> 0], "Expected a function over an empty domain")
        /\ Print(Tuple("seqLikeFunction:", seqLikeFunction))
        /\ Print(Tuple("incrementedSeq:", incrementedSeq))
        /\ Assert(incrementedSeq = <<2, 3, 4>>, "Expected each element to be incremented by 1")

Spec == Init /\ [][Next]_<<x>> /\ WF_[Next]_<<x>> /\ Inv
========================================
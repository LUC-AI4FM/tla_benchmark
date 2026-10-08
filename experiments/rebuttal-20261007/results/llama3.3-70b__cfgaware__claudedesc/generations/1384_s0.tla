```
MODULE Github648

EXTENDS Integers, TLC

CONSTANT Graph

VARIABLE v, w

TestGraph == LET RandomGraph == TLCEval(RandomElement(DirectedGraphs({1, 2, 3}))) IN
              [x |-> <<x, x>> : x \in {1, 2, 3}] \cup RandomGraph

DirectedGraphs(nodes) == {<<src, dst>> : src \in nodes, dst \in nodes}

BoundedSeq(S, n) == UNION {Sequences(S, i) : i \in 0..n}

BoundedSeqTLCEval(S, n) == TLCEval(BoundedSeq(S, n))

ASSUME Cardinality(BoundedSeqTLCEval(BoundedSeqTLCEval({1, 2}, 2), 2)) = 57

Init == (v \in {<<1, 1>>} /\ w \in {<<1, 1>>})

Next == (v' \in {e : e \in Graph} /\ w' \in {e : e \in TestGraph})

Inv == (v \in {e : e \in Graph} /\ 
        w \in {e : e \in TestGraph} /\
        TLCEval(TLCEval(Cardinality(BoundedSeqTLCEval(BoundedSeq({1, 2, 3}, 3), 3)))) = 65641)

THEOREM Inv => [](Inv)
```